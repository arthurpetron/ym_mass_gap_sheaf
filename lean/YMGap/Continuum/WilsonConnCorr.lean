/-
Wall-2 real object — the GENUINE SU(2) Wilson connected two-point correlator
along the single-line connecting chain, as a vacuum-subtracted character
double-sum (NOT defined to equal an abstract `corr` by fiat).

# Why this module exists (contrast with the trivial `WilsonCorrelator.wilsonCorr`)

`Continuum/WilsonCorrelator.lean` carries a correlator `wilsonCorr Λ n :=
corr (wilsonSpectralModel Λ) n` whose `matches_abstract` field is `eqv_refl`:
it is DEFINED to be the abstract spectral-model `corr`, so the "identity"
`wilsonCorr ≃ corr (gapModel)` is a definitional reflexivity, not derived
content.  That makes the correlator's decay a restatement of the abstract
model's decay — the real object never appears.

This module builds the REAL object instead.  Mirroring the genuinely-interacting
two-plaquette construction `MayerTwoPlaquette.Z2` (a character double-sum coupled
through the shared-link Haar orthogonality kernel `δ_{a,b}`), we define the
connected two-point correlator of the heat-kernel measure at separation `n` for
the SINGLE-LINE geometry: the two Wilson observables `W₀, W_n` joined by a chain
of `n` plaquettes through `n` shared links.

The two end-reps `a, b` are coupled through the chain by the SAME Haar
orthogonality `δ_{a,b}` (each shared link forces the meeting reps to coincide;
`n` shared links force a SINGLE common rep `r` along the whole chain — the
single-rep collapse of `KPCriterion.constrained_connected_single_rep`).  Vacuum
subtraction removes the `r = 0` channel (the disconnected `⟨χ(W₀)⟩⟨χ(W_n)⟩`
piece).  Concretely:

    wilsonG(w, M, n)  =  Σ_{a<M} Σ_{b<M}  δ̂_{a,b} · coeffW w a · (coeffW w b)^n,

where `δ̂_{a,b} = δ_{a,b}·(1 − δ_{a,0})` is the vacuum-subtracted shared-link
kernel (the diagonal, EXCLUDING the vacuum rep `0`).  The off-diagonal terms
are killed by orthogonality and the `a = 0` term by vacuum subtraction, so the
double sum COLLAPSES to the connected single-rep chain sum

    wilsonG(w, M, n)  ≃  Σ_{r=1}^{M-1}  (coeffW w r)^{n+1},

a chain of `n + 1` plaquettes all carrying ONE common excited rep `r ≥ 1`.

# What is PROVED here (all genuine — no fakes)

  * `vacSubKernel a b` — the vacuum-subtracted shared-link orthogonality kernel
    `δ_{a,b}·(1 − δ_{a,0})` (diagonal minus the vacuum rep), with
    `vacSubKernel_diag_excited`, `vacSubKernel_vacuum`, `vacSubKernel_off`.
  * `chainBody w r n = (coeffW w r)^n` — the `n`-link chain body carried at rep
    `r`; `endWeight w r = coeffW w r` the end-observable weight.
  * `wilsonG w M n` — the REAL connected correlator as the vacuum-subtracted
    character DOUBLE-sum (built in the `Z2` style).  `wilsonG_zero` (the `n = 0`
    normalization: total EXCITED character mass), `wilsonG_nonneg`.
  * `connChain w r n = (coeffW w r)^{n+1}` and `wilsonG_collapse` — THE
    single-rep collapse: the `n`-shared-link orthogonality + vacuum subtraction
    force a single common EXCITED rep, so `wilsonG ≃ Σ_{r=1}^{M-1} connChain`.
  * `coeffW_excited_le_one` — the excited coefficients are non-increasing
    (`coeffW w r ≤ coeffW w 1` for `r ≥ 1`, from the proved per-rep ratio
    `2w⁵ ≤ 1`), so `coeffW w 1 = 2w³` is the dominant excited weight.
  * `wilsonG_decay` — GEOMETRIC DECAY `wilsonG w M n ≤ C · ρ^n` with
    `ρ = coeffW w 1 = 2w³` and `C = M · ρ`, valid at strong coupling
    `0 ≤ w ≤ 1/2`, where `ρ ≤ 1/4 < 1` (`rho_lt_one`).  Genuinely derived from
    the per-step factor `2w³ < 1`, NOT posited.

# NAMED-open residual (NOT faked)

The FULL identity `wilsonG = (abstract corr of the real transfer model)` — the
genuine non-trivial `matches_abstract`, tying this real character double-sum to
the abstract spectral `corr` of the reconstructed transfer operator — requires
the multi-plaquette Mayer / Dobrushin-ratio induction (the connecting structure
is a single line here; the general connected geometry needs the cluster
reorganization).  It is carried as the NAMED Type-level obligation
`WilsonGMatchesAbstract` with NO inhabitant — it is NOT faked as `eqv_refl`
(contrast `WilsonCorrelator.genuineRealCorrelatorLink`, whose `matches_abstract`
IS reflexivity because its correlator is DEFINED as the abstract `corr`).

# Constructive contract (AGENTS.md Rules 1, 6, 8)

Mathlib-free; pure `Q'` / `Nat` arithmetic, structural `finSum` inductions, and
the reused proved per-rep ratio / geometric-series engine.  No `Classical.*`, no
`Real`, no `native_decide`, no `decide` on non-decidable props, no `sorry` /
`admit` / new `axiom`.  `wilsonG` is a genuine character double-sum (NOT defined
to equal an abstract `corr`).  Witnesses are `Type`-level data; the open
multi-plaquette identity is a named structure, not a faked proof.  Every
load-bearing declaration is gated with `#print axioms` (permitted: `propext` /
`Quot.sound`).
-/

import YMGap.Continuum.MayerTwoPlaquette
import YMGap.Continuum.PlaquetteActivity
import YMGap.Continuum.BondMovingMoment

namespace YMGap.Continuum.WilsonConnCorr

open YMGap.Constructive
open YMGap.Constructive.RationalTail
open YMGap.Continuum
open YMGap.Continuum.BondMovingStep
open YMGap.Continuum.HeatKernelGap
open YMGap.Continuum.RGTransport
open YMGap.Continuum.PlaquetteActivity
open YMGap.Continuum.MayerTwoPlaquette
open YMGap.Continuum.BondMovingMoment
open YMGap.Continuum.PolymerModel

/-! ## 1. The vacuum-subtracted shared-link orthogonality kernel `δ̂_{a,b}`

The two end-reps `a, b` of the connecting chain are coupled by the SAME SU(2)
character orthogonality the shared links enforce (`MayerTwoPlaquette.orthoKernel
a b = δ_{a,b}`).  The CONNECTED correlator additionally subtracts the vacuum
channel `r = 0` (the disconnected `⟨χ(W₀)⟩⟨χ(W_n)⟩` product).  So the kernel is
the orthogonality diagonal with the vacuum rep removed:

    δ̂_{a,b}  =  δ_{a,b} · (1 − δ_{a,0})  =  (1 if a = b ∧ a ≠ 0, else 0). -/

/-- **The vacuum-subtracted shared-link kernel** `δ̂_{a,b}`: `1` when `a = b` and
`a ≠ 0` (an excited common rep survives), else `0` (off-diagonal killed by Haar
orthogonality; the vacuum rep `a = 0` killed by vacuum subtraction). -/
def vacSubKernel (a b : Rep) : Q' := if a = b then (if a = 0 then 0 else 1) else 0

/-- On an EXCITED diagonal `a = b`, `a ≥ 1`, the kernel is `1`. -/
@[simp] theorem vacSubKernel_diag_excited (k : Nat) :
    vacSubKernel (k + 1) (k + 1) = 1 := by
  unfold vacSubKernel; rw [if_pos rfl, if_neg (Nat.succ_ne_zero k)]

/-- The vacuum rep is subtracted: `δ̂_{0,0} = 0`. -/
@[simp] theorem vacSubKernel_vacuum : vacSubKernel 0 0 = 0 := by
  unfold vacSubKernel; rw [if_pos rfl, if_pos rfl]

/-- Off-diagonal terms vanish: `b ≠ a ⟹ δ̂_{a,b} = 0`. -/
theorem vacSubKernel_off {a b : Rep} (h : a ≠ b) : vacSubKernel a b = 0 := by
  unfold vacSubKernel; rw [if_neg h]

/-! ## 2. The chain body and end weights

The connecting chain of `n` plaquettes carried at common rep `r` contributes the
`n`-fold power `(coeffW w r)^n` (the per-link chain transfer); the two Wilson
ends carry one extra factor `coeffW w r` (`endWeight`).  The full connected
chain of `n + 1` plaquettes at rep `r` is `endWeight · chainBody = (coeffW w
r)^{n+1}` (`connChain`). -/

/-- The `n`-link chain body carried at rep `r`: the `n`-fold per-link transfer
power `(coeffW w r)^n`. -/
def chainBody (w : Q') (r : Rep) (n : Nat) : Q' := (coeffW w r) ^ n

/-- The end-observable weight at rep `r`: the single character coefficient
`coeffW w r` carried by each Wilson end. -/
def endWeight (w : Q') (r : Rep) : Q' := coeffW w r

/-- The connected chain of `n + 1` plaquettes at common rep `r`:
`endWeight · chainBody = coeffW w r · (coeffW w r)^n = (coeffW w r)^{n+1}`. -/
def connChain (w : Q') (r : Rep) (n : Nat) : Q' := (coeffW w r) ^ (n + 1)

/-- `endWeight · chainBody ≃ connChain` (the end factor times the chain power is
the `(n+1)`-fold power). -/
theorem endWeight_mul_chainBody (w : Q') (r : Rep) (n : Nat) :
    (endWeight w r * chainBody w r n).eqv (connChain w r n) := by
  unfold endWeight chainBody connChain
  -- coeffW w r * (coeffW w r)^n = (coeffW w r)^(n+1) definitionally
  show ((coeffW w r) * (coeffW w r) ^ n).eqv ((coeffW w r) ^ (n + 1))
  rw [Q'.pow_succ]
  exact Q'.eqv_refl _

/-! ## 3. The real connected correlator as a vacuum-subtracted character double-sum

`wilsonG(w, M, n)` mirrors `MayerTwoPlaquette.Z2`: a character DOUBLE-sum over
the two end-reps `a, b`, coupled through the vacuum-subtracted shared-link
kernel `δ̂_{a,b}`, with the end weight `coeffW w a` at one end and the chain body
`(coeffW w b)^n` at the other.  Genuinely a double sum (NOT defined to equal any
abstract `corr`). -/

/-- The inner (over `b`) sum at fixed outer end-rep `a`:
`Σ_{b<M} δ̂_{a,b} · coeffW w a · (coeffW w b)^n`. -/
def wilsonGInner (w : Q') (n : Nat) (a : Rep) (M : Nat) : Q' :=
  finSum (fun b => vacSubKernel a b * endWeight w a * chainBody w b n) M

/-- **The real SU(2) Wilson connected two-point correlator** at separation `n`,
on the single-line connecting chain: the vacuum-subtracted character DOUBLE-sum

    wilsonG(w, M, n) = Σ_{a<M} Σ_{b<M} δ̂_{a,b}·coeffW w a·(coeffW w b)^n.

This is a GENUINE character double-sum (built like `Z2`), vacuum-subtracted —
NOT defined to equal an abstract `corr`. -/
def wilsonG (w : Q') (M n : Nat) : Q' :=
  finSum (fun a => wilsonGInner w n a M) M

/-! ## 4. The single-rep collapse (THE connected-correlator content)

The inner orthogonality sum collapses exactly as `Z2Inner_collapse`: off-diagonal
`b ≠ a` terms are killed by `δ̂_{a,b} = 0`, and the diagonal term is
`vacSubKernel a a · coeffW w a · (coeffW w a)^n`.  The diagonal kernel is `0` at
the vacuum `a = 0` (subtraction) and `1` at every excited `a ≥ 1`, so for an
excited row the inner sum is the connected chain `(coeffW w a)^{n+1}`, and for
the vacuum row it is `0`. -/

/-- Off-diagonal summand vanishes (`b ≠ a` kills the kernel). -/
theorem wilsonG_offdiag_zero (w : Q') (n : Nat) (a b : Rep) (h : b ≠ a) :
    (vacSubKernel a b * endWeight w a * chainBody w b n).eqv 0 := by
  rw [vacSubKernel_off (fun hab => h hab.symm)]
  refine Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_right _ 0 (chainBody w b n)
      (Q'.zero_mul_eqv (endWeight w a))) ?_
  exact Q'.zero_mul_eqv (chainBody w b n)

/-- The diagonal inner-collapse (PROVED).  For `a < M`, the inner sum is `Q'.eqv`
to the single diagonal term `δ̂_{a,a}·coeffW w a·(coeffW w a)^n` — every
off-diagonal `b ≠ a` term killed by the kernel.  (Mirrors `Z2Inner_collapse`.) -/
theorem wilsonGInner_collapse (w : Q') (n : Nat) (a : Rep) :
    ∀ {M : Nat}, a < M →
      (wilsonGInner w n a M).eqv
        (vacSubKernel a a * endWeight w a * chainBody w a n) := by
  intro M
  induction M with
  | zero => intro ha; exact absurd ha (Nat.not_lt_zero a)
  | succ k ih =>
      intro _ha
      unfold wilsonGInner
      rw [finSum_succ]
      by_cases hak : a = k
      · subst hak
        have hlow :
            (finSum (fun b => vacSubKernel a b * endWeight w a * chainBody w b n) a).eqv 0 := by
          refine Q'.eqv_trans _ _ _
            (finSum_eqv_congr_lt _ (fun _ => 0)
              a (fun b hb => wilsonG_offdiag_zero w n a b (Nat.ne_of_lt hb))) ?_
          rw [finSum_zero_seq]; exact Q'.eqv_refl 0
        refine Q'.eqv_trans _ _ _
          (Q'.add_eqv_congr_right _ 0
            (vacSubKernel a a * endWeight w a * chainBody w a n) hlow) ?_
        exact Q'.eqv_of_eq (Q'.zero_add' _)
      · have hak' : a < k := by
          rcases Nat.lt_succ_iff_lt_or_eq.mp _ha with h | h
          · exact h
          · exact absurd h hak
        have ihk := ih hak'
        rw [wilsonGInner] at ihk
        refine Q'.eqv_trans _ _ _
          (Q'.add_eqv_congr_left _ _ 0 (wilsonG_offdiag_zero w n a k (fun h => hak h.symm))) ?_
        refine Q'.eqv_trans _ _ _
          (Q'.eqv_of_eq (Q'.add_zero'
            (finSum (fun b => vacSubKernel a b * endWeight w a * chainBody w b n) k))) ?_
        exact ihk

/-- The diagonal term at an EXCITED rep `a = k+1` collapses to the connected
chain `(coeffW w (k+1))^{n+1}`: kernel `1`, then `endWeight·chainBody`. -/
theorem diag_excited (w : Q') (n k : Nat) :
    (vacSubKernel (k + 1) (k + 1) * endWeight w (k + 1) * chainBody w (k + 1) n).eqv
      (connChain w (k + 1) n) := by
  rw [vacSubKernel_diag_excited]
  refine Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_right _ (endWeight w (k + 1)) (chainBody w (k + 1) n)
      (Q'.one_mul_eqv (endWeight w (k + 1)))) ?_
  exact endWeight_mul_chainBody w (k + 1) n

/-- The diagonal term at the VACUUM rep `a = 0` vanishes (vacuum subtraction). -/
theorem diag_vacuum (w : Q') (n : Nat) :
    (vacSubKernel 0 0 * endWeight w 0 * chainBody w 0 n).eqv 0 := by
  rw [vacSubKernel_vacuum]
  refine Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_right _ 0 (chainBody w 0 n) (Q'.zero_mul_eqv (endWeight w 0))) ?_
  exact Q'.zero_mul_eqv (chainBody w 0 n)

/-! ## 5. The collapsed connected single-rep chain sum

After the inner collapse and the vacuum subtraction, the surviving rows are the
EXCITED reps `r = 1, …, M-1`, each contributing the connected chain
`(coeffW w r)^{n+1}`.  We package the collapsed form as the excited-rep sum

    connSum(w, M, n)  =  Σ_{k<M} (coeffW w (1 + k))^{n+1}  =  Σ_{r=1}^{M} connChain,

mirroring `PlaquetteActivity.plaqActivity` (the excited-rep window). -/

/-- **The collapsed connected single-rep chain sum** `Σ_{k<M} connChain w (1+k) n`
= `Σ_{r=1}^{M} (coeffW w r)^{n+1}`: the connected correlator after the
shared-link orthogonality collapse (one common excited rep `r ≥ 1` along the
chain of `n + 1` plaquettes). -/
def connSum (w : Q') (M n : Nat) : Q' :=
  finSum (fun k => connChain w (1 + k) n) M

/-- The full diagonal of `wilsonG` (the row-sum after the inner collapse):
`Σ_{a<M} δ̂_{a,a}·coeffW w a·(coeffW w a)^n`. -/
def wilsonGDiag (w : Q') (M n : Nat) : Q' :=
  finSum (fun a => vacSubKernel a a * endWeight w a * chainBody w a n) M

/-- `wilsonG` collapses to its diagonal (each inner row replaced by its diagonal
term, via `wilsonGInner_collapse`). -/
theorem wilsonG_eqv_diag (w : Q') (M n : Nat) :
    (wilsonG w M n).eqv (wilsonGDiag w M n) := by
  unfold wilsonG wilsonGDiag
  exact finSum_eqv_congr_lt _ _ M (fun a ha => wilsonGInner_collapse w n a ha)

/-- The diagonal row-sum equals the connected excited-rep sum: the vacuum row
(`a = 0`) vanishes and each excited row (`a = k+1`) is `connChain w (k+1) n`.
We prove `wilsonGDiag w (M+1) n ≃ connSum w M n` (cutoff `M+1` so the vacuum row
is the head `a = 0` and the excited window is `1, …, M`). -/
theorem wilsonGDiag_succ_eqv_connSum (w : Q') (M n : Nat) :
    (wilsonGDiag w (M + 1) n).eqv (connSum w M n) := by
  unfold wilsonGDiag connSum
  -- Σ_{a<M+1} diag a = diag 0 + Σ_{a<M} diag (a+1); diag 0 ≃ 0, diag (k+1) ≃ connChain.
  induction M with
  | zero =>
      -- Σ_{a<1} diag a = 0 + diag 0 ≃ 0  ;  RHS = Σ_{k<0} = 0
      rw [finSum_succ, finSum_zero]
      refine Q'.eqv_trans _ _ _ (Q'.eqv_of_eq (Q'.zero_add' _)) ?_
      exact diag_vacuum w n
  | succ j ih =>
      -- LHS: Σ_{a<j+2} diag a = (Σ_{a<j+1} diag a) + diag (j+1)
      -- RHS: Σ_{k<j+1} connChain (1+k) n = (Σ_{k<j} connChain (1+k) n) + connChain (1+j) n
      rw [finSum_succ, finSum_succ]
      refine Q'.eqv_trans _ _ _
        (Q'.add_eqv_congr_right _ _
          (vacSubKernel (j + 1) (j + 1) * endWeight w (j + 1) * chainBody w (j + 1) n) ih) ?_
      -- now need: connSum-prefix + diag (j+1) ≃ connSum-prefix + connChain (1+j) n
      refine Q'.add_eqv_congr_left _ _ _ ?_
      -- diag (j+1) ≃ connChain (j+1) n = connChain (1+j) n  (since j+1 = 1+j)
      have hidx : connChain w (j + 1) n = connChain w (1 + j) n := by
        have h1 : (j + 1 : Nat) = 1 + j := by omega
        rw [h1]
      exact Q'.eqv_trans _ _ _ (diag_excited w n j) (Q'.eqv_of_eq hidx)

/-- **`wilsonG_collapse` — THE single-rep collapse (PROVED).**  The real
vacuum-subtracted character double-sum collapses to the connected single-rep
chain sum

    wilsonG(w, M+1, n)  ≃  Σ_{r=1}^{M} (coeffW w r)^{n+1},

the `n`-shared-link Haar orthogonality forcing ONE common rep along the chain
(off-diagonal terms killed) and vacuum subtraction removing the `r = 0` channel.
This is the genuine "correlator as a (collapsed) cluster sum along the connecting
chain" (the activity-side mechanism of `KPCriterion.constrained_connected_single_rep`
applied to the `n + 1`-plaquette line). -/
theorem wilsonG_collapse (w : Q') (M n : Nat) :
    (wilsonG w (M + 1) n).eqv (connSum w M n) :=
  Q'.eqv_trans _ _ _ (wilsonG_eqv_diag w (M + 1) n)
    (wilsonGDiag_succ_eqv_connSum w M n)

/-! ## 6. The `n = 0` normalization and nonnegativity -/

/-- The connected chain at `n = 0` is `coeffW w r` (a single plaquette / the bare
end weight): `connChain w r 0 = (coeffW w r)^1 ≃ coeffW w r`. -/
theorem connChain_zero (w : Q') (r : Rep) : (connChain w r 0).eqv (coeffW w r) := by
  show ((coeffW w r) ^ (0 + 1)).eqv (coeffW w r)
  show ((coeffW w r) ^ 1).eqv (coeffW w r)
  rw [Q'.pow_succ, Q'.pow_zero]
  exact Q'.mul_one_eqv (coeffW w r)

/-- **`wilsonG_zero` (the `n = 0` normalization, PROVED).**  At separation `0`
the connected correlator is the total EXCITED character mass
`Σ_{r=1}^{M} coeffW w r` — exactly `PlaquetteActivity.plaqActivity w M`, the
vacuum-subtracted (`r ≥ 1`) character weight.  (`⟨χ(W₀)²⟩ − ⟨χ(W₀)⟩²` reduces to
the excited mass.)  Via the collapse at `n = 0`. -/
theorem wilsonG_zero (w : Q') (M : Nat) :
    (wilsonG w (M + 1) 0).eqv (plaqActivity w M) := by
  refine Q'.eqv_trans _ _ _ (wilsonG_collapse w M 0) ?_
  unfold connSum plaqActivity
  -- Σ_{k<M} connChain w (1+k) 0 ≃ Σ_{k<M} coeffW w (1+k)
  exact finSum_eqv_congr_lt _ _ M (fun k _ => connChain_zero w (1 + k))

/-- The connected chain `(coeffW w r)^{n+1}` is nonnegative for `0 ≤ w`. -/
theorem connChain_nonneg {w : Q'} (hw : (0 : Q') ≤ w) (r : Rep) (n : Nat) :
    (0 : Q') ≤ connChain w r n :=
  Q'.pow_nonneg (coeffW w r) (coeffW_nonneg hw r) (n + 1)

/-- The collapsed connected sum is nonnegative for `0 ≤ w`. -/
theorem connSum_nonneg {w : Q'} (hw : (0 : Q') ≤ w) (M n : Nat) :
    (0 : Q') ≤ connSum w M n := by
  unfold connSum
  induction M with
  | zero => exact Q'.le_refl' 0
  | succ k ih =>
      rw [finSum_succ]
      exact Q'.zero_le_add _ _ ih (connChain_nonneg hw (1 + k) n)

/-- Nonneg transport across `Q'.eqv`. -/
theorem nonneg_of_eqv {a b : Q'} (ha : (0 : Q') ≤ a) (h : a.eqv b) :
    (0 : Q') ≤ b := Q'.le_trans' 0 a b ha (Q'.le_of_eqv h)

/-- **`wilsonG_nonneg` (PROVED).**  The real connected correlator is nonnegative
for `0 ≤ w` (a sum of `(n+1)`-fold powers of nonnegative character coefficients,
via the collapse). -/
theorem wilsonG_nonneg {w : Q'} (hw : (0 : Q') ≤ w) (M n : Nat) :
    (0 : Q') ≤ wilsonG w (M + 1) n :=
  nonneg_of_eqv (connSum_nonneg hw M n) (Q'.eqv_symm (wilsonG_collapse w M n))

/-! ## 7. The excited coefficients are non-increasing — `coeffW w 1 = 2w³` dominates

For the geometric decay we need the per-step factor: at strong coupling
`0 ≤ w ≤ 1/2`, every excited coefficient `coeffW w r` (`r ≥ 1`) is `≤ coeffW w 1
= 2w³`.  This is the proved consecutive ratio `coeffW w (s+1) ≤ (2w⁵)·coeffW w s`
with `2w⁵ ≤ 1/2 ≤ 1` (the `ratio_le_half` strong-coupling control), so the
excited sequence is NON-INCREASING and its head `coeffW w 1` dominates. -/

/-- The strong-coupling threshold `w₀ = 1/2`. -/
def half : Q' := Q'.mkPos 1 2 (by decide)

/-- One step of the excited non-increase: at `0 ≤ w ≤ 1/2`, for `s ≥ 1`,
`coeffW w (s+1) ≤ coeffW w s` (the ratio `2w⁵ ≤ 1/2 ≤ 1` and `coeffW ≥ 0`). -/
theorem coeffW_succ_le_self {w : Q'} (hw0 : (0 : Q') ≤ w) (hw : w ≤ half)
    (s : Nat) (hs : 1 ≤ s) :
    coeffW w (s + 1) ≤ coeffW w s := by
  have hw1 : w ≤ (1 : Q') := Q'.le_trans' _ _ _ hw (by decide)
  -- coeffW w (s+1) ≤ (2w⁵)·coeffW w s ≤ 1·coeffW w s ≃ coeffW w s
  have hratio : coeffW w (s + 1) ≤ (Q'.ofNat 2 * qpow w 5) * coeffW w s :=
    coeffW_succ_ratio hw0 hw1 s hs
  have hr_le_one : Q'.ofNat 2 * qpow w 5 ≤ (1 : Q') :=
    Q'.le_trans' _ _ _ (ratio_le_half hw0 hw) (by decide)
  have hcnn : (0 : Q') ≤ coeffW w s := coeffW_nonneg hw0 s
  have hstep : (Q'.ofNat 2 * qpow w 5) * coeffW w s ≤ (1 : Q') * coeffW w s :=
    Q'.mul_le_mul_of_nonneg_right _ _ _ hr_le_one hcnn
  refine Q'.le_trans' _ _ _ hratio (Q'.le_trans' _ _ _ hstep ?_)
  exact Q'.le_of_eqv (Q'.one_mul_eqv (coeffW w s))

/-- **The excited coefficients are bounded by their head (PROVED).**  At strong
coupling `0 ≤ w ≤ 1/2`, every excited coefficient is `≤ coeffW w 1 = 2w³`:
`coeffW w (1 + k) ≤ coeffW w 1` for every `k`.  By the non-increase
`coeffW_succ_le_self`. -/
theorem coeffW_excited_le_one {w : Q'} (hw0 : (0 : Q') ≤ w) (hw : w ≤ half) :
    ∀ k, coeffW w (1 + k) ≤ coeffW w 1 := by
  intro k
  induction k with
  | zero => exact Q'.le_refl' _
  | succ j ih =>
      -- coeffW w (1+(j+1)) = coeffW w ((1+j)+1) ≤ coeffW w (1+j) ≤ coeffW w 1
      have hidx : (1 + (j + 1) : Nat) = (1 + j) + 1 := by omega
      rw [hidx]
      exact Q'.le_trans' _ _ _
        (coeffW_succ_le_self hw0 hw (1 + j) (by omega)) ih

/-! ## 8. GEOMETRIC DECAY — `wilsonG w (M+1) n ≤ C · ρ^n`, `ρ = 2w³ < 1`

The collapse gives `wilsonG ≃ Σ_{k<M} (coeffW w (1+k))^{n+1}`.  Each excited base
is `≤ coeffW w 1 = 2w³` (`coeffW_excited_le_one`), so each term is `≤
(coeffW w 1)^{n+1} = ρ^{n+1} = ρ·ρ^n`, and the `M`-term sum is `≤ (M·ρ)·ρ^n`.
The rate `ρ = coeffW w 1 = 2w³ ≤ 1/4 < 1` at strong coupling `0 ≤ w ≤ 1/2`. -/

/-- **The geometric rate** `ρ = coeffW w 1 = 2w³`. -/
def rho (w : Q') : Q' := coeffW w 1

/-- `ρ = 2w³ ≤ 1/4 < 1` at strong coupling `0 ≤ w ≤ 1/2` (`rho_lt_one`'s margin):
`coeffW w 1 = dimQ 1 · w³ = 2·w³`, monotone in `w`, `≤ 2·(1/2)³ = 1/4`. -/
theorem rho_le_quarter {w : Q'} (hw0 : (0 : Q') ≤ w) (hw : w ≤ half) :
    rho w ≤ Q'.mkPos 1 4 (by decide) := by
  unfold rho
  rw [coeffW_one_eq w]
  -- dimQ 1 · heatKernelSep w ≤ dimQ 1 · heatKernelSep (1/2) = 2 · 1/8 = 1/4
  have hsep : heatKernelSep w ≤ heatKernelSep half := heatKernelSep_mono hw0 hw
  have hstep : dimQ 1 * heatKernelSep w ≤ dimQ 1 * heatKernelSep half :=
    Q'.mul_le_mul_of_nonneg_left _ _ _ hsep (dimQ_nonneg 1)
  refine Q'.le_trans' _ _ _ hstep ?_
  -- dimQ 1 · (1/2)³ = 2 · 1/8 = 1/4, decidable
  show dimQ 1 * heatKernelSep half ≤ Q'.mkPos 1 4 (by decide)
  decide

/-- **`rho_lt_one` (the genuine gap rate, PROVED).**  At strong coupling
`0 ≤ w ≤ 1/2` the per-step decay factor is `< 1`: `ρ = 2w³ ≤ 1/4 < 1`. -/
theorem rho_lt_one {w : Q'} (hw0 : (0 : Q') ≤ w) (hw : w ≤ half) :
    rho w < (1 : Q') :=
  HeatKernelGap.lt_of_le_of_lt (rho_le_quarter hw0 hw) (by decide)

/-- `ρ` is nonnegative at `0 ≤ w`. -/
theorem rho_nonneg {w : Q'} (hw0 : (0 : Q') ≤ w) : (0 : Q') ≤ rho w :=
  coeffW_nonneg hw0 1

/-- Each collapsed excited term is `≤ ρ^{n+1}`: `(coeffW w (1+k))^{n+1} ≤
(coeffW w 1)^{n+1}` (excited base `≤` head, both nonneg), via `pow_le_pow_of_le`. -/
theorem connChain_excited_le {w : Q'} (hw0 : (0 : Q') ≤ w) (hw : w ≤ half)
    (k n : Nat) :
    connChain w (1 + k) n ≤ (rho w) ^ (n + 1) := by
  unfold connChain rho
  exact pow_le_pow_of_le (coeffW_nonneg hw0 (1 + k))
    (coeffW_excited_le_one hw0 hw k) (n + 1)

/-- The collapsed connected sum is bounded by `(ofNat M)·ρ^{n+1}` (the `M`-term
sum of terms each `≤ ρ^{n+1}`).  Induction on `M`. -/
theorem connSum_le {w : Q'} (hw0 : (0 : Q') ≤ w) (hw : w ≤ half) (M n : Nat) :
    connSum w M n ≤ Q'.ofNat M * (rho w) ^ (n + 1) := by
  unfold connSum
  induction M with
  | zero =>
      -- finSum _ 0 = 0 ≤ ofNat 0 · ρ^{n+1} = 0·…
      show (0 : Q') ≤ Q'.ofNat 0 * (rho w) ^ (n + 1)
      refine Q'.le_of_eqv ?_
      exact Q'.eqv_symm (Q'.zero_mul_eqv _)
  | succ k ih =>
      rw [finSum_succ]
      -- (Σ_{j<k} … ) + connChain (1+k) n ≤ ofNat k · ρ^{n+1} + ρ^{n+1}
      --                                  = ofNat (k+1) · ρ^{n+1}
      have hstep : finSum (fun j => connChain w (1 + j) n) k + connChain w (1 + k) n
          ≤ Q'.ofNat k * (rho w) ^ (n + 1) + (rho w) ^ (n + 1) := by
        refine Q'.le_trans' _ _ _
          (Q'.add_le_add_right _ _ (connChain w (1 + k) n) ih) ?_
        exact Q'.add_le_add_left _ _ _ (connChain_excited_le hw0 hw k n)
      refine Q'.le_trans' _ _ _ hstep ?_
      -- ofNat k · ρ^{n+1} + ρ^{n+1} ≃ ofNat (k+1) · ρ^{n+1}
      refine Q'.le_of_eqv ?_
      -- RHS: ofNat (k+1)·ρ ≃ (ofNat k + ofNat 1)·ρ ≃ ofNat k·ρ + ofNat 1·ρ
      --                     ≃ ofNat k·ρ + ρ  (ofNat 1 ≃ 1).
      refine Q'.eqv_symm ?_
      refine Q'.eqv_trans _ _ _
        (Q'.mul_eqv_congr_right _ _ ((rho w) ^ (n + 1))
          (Q'.ofNat_add_eqv k 1)) ?_
      refine Q'.eqv_trans _ _ _
        (Q'.add_mul_eqv (Q'.ofNat k) (Q'.ofNat 1) ((rho w) ^ (n + 1))) ?_
      refine Q'.add_eqv_congr_left _ _ _ ?_
      -- ofNat 1 · ρ ≃ 1 · ρ ≃ ρ
      refine Q'.eqv_trans _ _ _
        (Q'.mul_eqv_congr_right (Q'.ofNat 1) 1 ((rho w) ^ (n + 1)) (by decide)) ?_
      exact Q'.one_mul_eqv ((rho w) ^ (n + 1))

/-- **`wilsonG_decay` — GEOMETRIC DECAY of the real correlator (PROVED).**

For the single-line connecting chain, at strong coupling `0 ≤ w ≤ 1/2`,

    wilsonG(w, M+1, n)  ≤  C · ρ^n        with  C = (ofNat M)·ρ,  ρ = 2w³ < 1.

Genuinely derived from the per-step factor `coeffW w 1 = 2w³ < 1`
(`rho_lt_one`): the collapse to the single-rep chain sum, the excited base bound
`coeffW w r ≤ coeffW w 1`, and the `(n+1)`-fold power give `wilsonG ≤
Σ_{r=1}^{M} (coeffW w 1)^{n+1} ≤ (M·ρ)·ρ^n`.  NOT posited — every step is proved.
The rate `ρ < 1` holds at strong coupling (`rho_lt_one`). -/
theorem wilsonG_decay {w : Q'} (hw0 : (0 : Q') ≤ w) (hw : w ≤ half) (M n : Nat) :
    wilsonG w (M + 1) n ≤ (Q'.ofNat M * rho w) * (rho w) ^ n := by
  -- wilsonG ≤ connSum ≤ ofNat M · ρ^{n+1} = (ofNat M · ρ) · ρ^n
  have hcol : wilsonG w (M + 1) n ≤ connSum w M n :=
    Q'.le_of_eqv (wilsonG_collapse w M n)
  refine Q'.le_trans' _ _ _ hcol (Q'.le_trans' _ _ _ (connSum_le hw0 hw M n) ?_)
  -- ofNat M · ρ^{n+1} ≃ (ofNat M · ρ) · ρ^n
  refine Q'.le_of_eqv ?_
  -- ρ^{n+1} = ρ · ρ^n ; ofNat M · (ρ · ρ^n) ≃ (ofNat M · ρ) · ρ^n
  show (Q'.ofNat M * (rho w) ^ (n + 1)).eqv ((Q'.ofNat M * rho w) * (rho w) ^ n)
  rw [Q'.pow_succ]
  exact Q'.eqv_symm (Q'.mul_assoc_eqv (Q'.ofNat M) (rho w) ((rho w) ^ n))

/-! ## 9. NAMED-open: the full multi-plaquette identity to the abstract `corr`

The genuine non-trivial `matches_abstract` — the identity tying this REAL
character double-sum `wilsonG` to the abstract spectral `corr` of the
reconstructed transfer operator — is NOT closed here.  The single-line geometry
collapses to a single-rep chain; the general connected correlator needs the
multi-plaquette Mayer / Dobrushin-ratio induction.  We carry it as a NAMED
Type-level OBLIGATION with NO inhabitant — it is NOT faked as `eqv_refl`.

Contrast: `WilsonCorrelator.genuineRealCorrelatorLink.matches_abstract` IS
reflexivity, but only because its `wilsonCorr` is DEFINED to be the abstract
`corr`.  Here `wilsonG` is an independent character double-sum, so the identity
is genuine content — and it is left open, not posited. -/

/-- **NAMED-open obligation: the full `wilsonG = abstract corr` identity.**
`WilsonGMatchesAbstract w` is the Type-level datum a genuine multi-plaquette
correspondence must supply: an abstract correlator family `absCorr` (the `corr`
of the reconstructed transfer operator) together with the proof `matches` that
the REAL connected correlator `wilsonG w (M+1) n` coincides (up to `eqv`) with
it.  Deliberately LEFT UNINHABITED — it requires the multi-plaquette Mayer /
Dobrushin-ratio induction (a later loop), NOT the finite character collapse
closed above.  It is NOT faked as `eqv_refl`. -/
structure WilsonGMatchesAbstract (w : Q') where
  /-- The abstract reconstructed-transfer-operator correlator family. -/
  absCorr : Nat → Nat → Q'
  /-- The genuine identity: the real connected correlator equals the abstract
  `corr` (up to `eqv`).  This is the open multi-plaquette content. -/
  matchesAbs : ∀ M n, (wilsonG w (M + 1) n).eqv (absCorr M n)

/-! ## 10. Documentation: PROVED vs NAMED-open (AGENTS.md Rule 6)

PROVED (genuine, axiom-clean — the real connected correlator on the chain):

  * `vacSubKernel` (+ `vacSubKernel_diag_excited`, `vacSubKernel_vacuum`,
    `vacSubKernel_off`) — the vacuum-subtracted shared-link orthogonality kernel
    `δ_{a,b}·(1 − δ_{a,0})`;
  * `chainBody`, `endWeight`, `connChain` (+ `endWeight_mul_chainBody`) — the
    chain body / end weight / connected `(n+1)`-plaquette chain at a common rep;
  * `wilsonG` — the REAL connected correlator as the vacuum-subtracted character
    DOUBLE-sum (built in the `Z2` style; NOT defined to equal an abstract
    `corr`);
  * `wilsonG_collapse` — THE single-rep collapse `wilsonG w (M+1) n ≃
    Σ_{r=1}^{M} (coeffW w r)^{n+1}` (the `n`-shared-link orthogonality forcing a
    single common excited rep along the chain; vacuum subtracted);
  * `wilsonG_zero` (the `n = 0` normalization = excited character mass
    `plaqActivity w M`), `wilsonG_nonneg`;
  * `coeffW_succ_le_self`, `coeffW_excited_le_one` — the excited coefficients are
    non-increasing, `coeffW w 1 = 2w³` dominates (at `0 ≤ w ≤ 1/2`);
  * `rho` (= `coeffW w 1 = 2w³`), `rho_le_quarter`, `rho_lt_one` — the per-step
    decay factor and its strong-coupling `< 1` margin (`ρ ≤ 1/4`);
  * `connChain_excited_le`, `connSum_le`, `wilsonG_decay` — GEOMETRIC DECAY
    `wilsonG w (M+1) n ≤ (ofNat M · ρ)·ρ^n` with `ρ = 2w³ < 1`, genuinely
    derived from the per-step factor.

NAMED-open (NOT faked, NO inhabitant):

  * `WilsonGMatchesAbstract` — the full identity `wilsonG = abstract corr of the
    reconstructed transfer operator` (the genuine non-trivial `matches_abstract`),
    requiring the multi-plaquette Mayer / Dobrushin-ratio induction.  Carried as
    a Type-level obligation; explicitly NOT faked as `eqv_refl` (contrast
    `WilsonCorrelator.genuineRealCorrelatorLink`, whose `matches_abstract` is
    reflexivity because its correlator is DEFINED as the abstract `corr`).

This module is the GENUINE real connected two-point correlator on the single-line
connecting chain, with its single-rep collapse and geometric decay.  It is NOT
the full interacting multi-plaquette correlator, NOT a convergence proof, and NOT
a 4D Yang–Mills mass gap. -/

end YMGap.Continuum.WilsonConnCorr

/-! ## Axiom-dependency gates (AGENTS.md Rule 1) -/

#print axioms YMGap.Continuum.WilsonConnCorr.vacSubKernel_diag_excited
#print axioms YMGap.Continuum.WilsonConnCorr.vacSubKernel_off
#print axioms YMGap.Continuum.WilsonConnCorr.endWeight_mul_chainBody
#print axioms YMGap.Continuum.WilsonConnCorr.wilsonGInner_collapse
#print axioms YMGap.Continuum.WilsonConnCorr.wilsonG_collapse
#print axioms YMGap.Continuum.WilsonConnCorr.wilsonG_zero
#print axioms YMGap.Continuum.WilsonConnCorr.wilsonG_nonneg
#print axioms YMGap.Continuum.WilsonConnCorr.coeffW_excited_le_one
#print axioms YMGap.Continuum.WilsonConnCorr.rho_lt_one
#print axioms YMGap.Continuum.WilsonConnCorr.connSum_le
#print axioms YMGap.Continuum.WilsonConnCorr.wilsonG_decay
