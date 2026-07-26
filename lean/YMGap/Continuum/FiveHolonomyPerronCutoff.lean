/-
BF4 five-holonomy Perron budget: an exact moving-cutoff closure over `Q'`.

This module formalises the quantitative algebra in
`notes/bf4-five-holonomy-perron-budget.md` without asserting the missing
nonlinear operator estimate.

The proved chain is:

1. For the SU(2) heat-kernel coefficients
     a_j(q) = (2j+1) q^{j(j+1)},
   the already-proved Casimir ratio estimate
     a_{N+l} <= a_N rho^l,  rho = 2 q^{2(N+1)}
   and the constructive geometric-series engine imply, whenever `rho <= 1/2`,
     sum_{l<M} a_{N+l} <= 2 a_N
   for every finite `M`.  Consequently every all-label partial sum is bounded
   by the computable cutoff ceiling
     sum_{j<N} a_j + 2 a_N.

2. A cutoff certificate compares that ceiling with `4^B` times a positive
   lower coefficient.  The five-holonomy geometry consumes the proved
   all-label bound and contributes the explicit 48 tensor factors; the Perron
   comparison contributes the explicit fourth power.  Thus
     C_s^2 <= 4^(192 B).

3. If the nonlinear spectral ratio obeys `0 <= q_s <= 1/4` and
     192 B + 1 <= m - 2,
   exact rational power arithmetic gives
     C_s^2 q_s^(m-2) <= 1/4 < 1.

HONEST SCOPE.  The coefficient tail and moving-cutoff arithmetic are proved
here.  `FiveHolonomyGeometry.kernel_from_allLabel` is the semantic
five-holonomy tensor-product estimate, and
`NonlinearSpectralCertificate.qS_le_quarter` is the genuinely missing
nonlinear spectral input.  This module does not construct either input and
does not close the Yang--Mills mass-gap frontier.

# Axiom gate

Pure `Q'`/`Nat` data, with witnesses carried in `Type`.  No `Classical.*`,
`native_decide`, `sorry`, or custom axioms.
-/

import YMGap.Continuum.TruncationTailChannelBound
import YMGap.Continuum.SU2HeatChannelHilbertSchmidtCompletion

namespace YMGap.Continuum.FiveHolonomyPerronCutoff

open YMGap.Constructive
open YMGap.Constructive.RationalTail
open YMGap.Continuum
open YMGap.Continuum.TruncationTailChannelBound
open YMGap.Continuum.SU2HeatChannelHilbertSchmidtCompletion

/-! ## 1. Exact coefficient-tail ceiling -/

/-- The geometric ratio furnished by the SU(2) Casimir increment past `N`. -/
def discardedRatio (nome : Q') (N : Nat) : Q' :=
  Q'.ofNat 2 * nome ^ (2 * (N + 1))

/-- The finite discarded-label sum starting at label `N`. -/
def discardedPartial (nome : Q') (N M : Nat) : Q' :=
  finSum (fun l => chanCoeff nome (N + l)) M

/-- The computable all-label ceiling: exact finite head plus twice the first
omitted coefficient. -/
def onePlaquetteCeiling (nome : Q') (N : Nat) : Q' :=
  finSum (chanCoeff nome) N + chanCoeff nome N * Q'.ofNat 2

/-- The discarded ratio is nonnegative for a nonnegative nome. -/
theorem discardedRatio_nonneg {nome : Q'} (hnome0 : (0 : Q') ≤ nome) (N : Nat) :
    (0 : Q') ≤ discardedRatio nome N :=
  Q'.mul_nonneg _ _ (by decide) (Q'.pow_nonneg nome hnome0 _)

/-- A geometric series of ratio `rho <= 1/2` has every partial sum bounded by
`2`.  This is derived from `CharacterTail.geom_series_le`, not assumed. -/
theorem geometricPartial_le_two {rho : Q'}
    (hrho0 : (0 : Q') ≤ rho)
    (hrhoHalf : rho ≤ Q'.mkPos 1 2 (by decide)) :
    ∀ M, finSum (fun l => rho ^ l) M ≤ Q'.ofNat 2 := by
  have hrec :
      (1 : Q') + rho * Q'.ofNat 2 ≤ Q'.ofNat 2 := by
    have hmul :
        rho * Q'.ofNat 2
          ≤ Q'.mkPos 1 2 (by decide) * Q'.ofNat 2 :=
      Q'.mul_le_mul_of_nonneg_right _ _ _ hrhoHalf (by decide)
    have hmulOne : rho * Q'.ofNat 2 ≤ (1 : Q') :=
      Q'.le_trans' _ _ _ hmul (Q'.le_of_eqv (by decide))
    exact Q'.le_trans' _ _ _
      (Q'.add_le_add_left 1 _ _ hmulOne)
      (Q'.le_of_eqv (by decide))
  refine YMGap.Constructive.CharacterTail.geom_series_le
    (fun l => rho ^ l) 1 rho (Q'.ofNat 2)
    hrho0 (by decide) ?_ ?_ hrec
  · show rho ^ 0 ≤ (1 : Q')
    exact Q'.le_refl' 1
  · intro l
    show rho ^ (l + 1) ≤ rho * rho ^ l
    exact Q'.le_refl' _

/-- The genuine all-label tail estimate:
`sum_{l<M} a_{N+l} <= 2 a_N`.

The proof consumes the existing super-geometric coefficient estimate
`chanCoeff_geoDom` and then sums its geometric majorant. -/
theorem discardedPartial_le_twoLead
    {nome : Q'} (hnome0 : (0 : Q') ≤ nome) (hnome1 : nome ≤ 1)
    (N : Nat) (hN1 : 1 ≤ N)
    (hratioHalf : discardedRatio nome N ≤ Q'.mkPos 1 2 (by decide))
    (M : Nat) :
    discardedPartial nome N M ≤ chanCoeff nome N * Q'.ofNat 2 := by
  have hterm :
      ∀ l, chanCoeff nome (N + l)
        ≤ chanCoeff nome N * discardedRatio nome N ^ l := by
    intro l
    exact chanCoeff_geoDom hnome0 hnome1 N hN1 l
  have hsum :
      finSum (fun l => chanCoeff nome (N + l)) M
        ≤ finSum (fun l => chanCoeff nome N * discardedRatio nome N ^ l) M :=
    YMGap.Constructive.CharacterTail.finSum_le_termwise _ _ hterm M
  have hgeom :
      finSum (fun l => discardedRatio nome N ^ l) M ≤ Q'.ofNat 2 :=
    geometricPartial_le_two (discardedRatio_nonneg hnome0 N) hratioHalf M
  have hpull :
      finSum (fun l => chanCoeff nome N * discardedRatio nome N ^ l) M
        ≤ chanCoeff nome N * Q'.ofNat 2 := by
    exact Q'.le_trans' _ _ _
      (Q'.le_of_eqv (Q'.eqv_symm
        (RationalTail.const_mul_finSum
          (fun l => discardedRatio nome N ^ l) (chanCoeff nome N) M)))
      (Q'.mul_le_mul_of_nonneg_left _ _ _ hgeom
        (chanCoeff_nonneg hnome0 N))
  exact Q'.le_trans' _ _ _ hsum hpull

/-- Exact prefix/tail split for the project's recursive finite sum. -/
theorem finSum_split (f : Nat → Q') (N : Nat) :
    ∀ M, (finSum f (N + M)).eqv
      (finSum f N + finSum (fun l => f (N + l)) M)
  | 0 => by
      rw [Nat.add_zero, finSum_zero, Q'.add_zero']
      exact Q'.eqv_refl _
  | M + 1 => by
      have ih := finSum_split f N M
      show (finSum f (N + M) + f (N + M)).eqv
        (finSum f N + (finSum (fun l => f (N + l)) M + f (N + M)))
      exact Q'.eqv_trans _ _ _
        (Q'.add_eqv_congr_right _ _ _ ih)
        (Q'.add_assoc_eqv _ _ _)

/-- Every partial sum extending past `N` is bounded by the computable
one-plaquette ceiling. -/
theorem extendedPartial_le_ceiling
    {nome : Q'} (hnome0 : (0 : Q') ≤ nome) (hnome1 : nome ≤ 1)
    (N : Nat) (hN1 : 1 ≤ N)
    (hratioHalf : discardedRatio nome N ≤ Q'.mkPos 1 2 (by decide))
    (M : Nat) :
    finSum (chanCoeff nome) (N + M) ≤ onePlaquetteCeiling nome N := by
  have hsplit := finSum_split (chanCoeff nome) N M
  have htail :=
    discardedPartial_le_twoLead hnome0 hnome1 N hN1 hratioHalf M
  exact Q'.le_trans' _ _ _
    (Q'.le_of_eqv hsplit)
    (Q'.add_le_add_left _ _ _ htail)

/-- **Uniform all-label ceiling.**  Every finite character partial sum,
including those below the cutoff, is bounded by `onePlaquetteCeiling`. -/
theorem allLabelPartial_le_ceiling
    {nome : Q'} (hnome0 : (0 : Q') ≤ nome) (hnome1 : nome ≤ 1)
    (N : Nat) (hN1 : 1 ≤ N)
    (hratioHalf : discardedRatio nome N ≤ Q'.mkPos 1 2 (by decide)) :
    ∀ K, finSum (chanCoeff nome) K ≤ onePlaquetteCeiling nome N := by
  intro K
  by_cases hKN : K ≤ N
  · have hprefix :
        finSum (chanCoeff nome) K ≤ finSum (chanCoeff nome) N :=
      RationalTail.finSum_monotone_of_nonneg
        (chanCoeff nome) (chanCoeff_nonneg hnome0) K N hKN
    have htailNonneg :
        (0 : Q') ≤ chanCoeff nome N * Q'.ofNat 2 :=
      Q'.mul_nonneg _ _ (chanCoeff_nonneg hnome0 N) (by decide)
    exact Q'.le_trans' _ _ _ hprefix
      (Q'.add_le_self_of_nonneg _ _ htailNonneg)
  · have hNK : N ≤ K := by omega
    obtain ⟨M, rfl⟩ := Nat.exists_eq_add_of_le hNK
    exact extendedPartial_le_ceiling hnome0 hnome1 N hN1 hratioHalf M

/-! ### A spacing-dependent cutoff constructed from the nome

The preceding theorem accepts any cutoff whose Casimir ratio is at most
`1/2`.  Here that cutoff is constructed explicitly from the general-base
power modulus.  For `0 < nome < 1`, first choose

`n₀ = powBaseCutoff nome (1/4)`,

so `nome^n₀ ≤ 1/4`, and then take `N = n₀+1`.  Since
`n₀ ≤ 2(N+1)`, antitonicity of powers gives

`2 * nome^(2(N+1)) ≤ 2 * (1/4) = 1/2`.

Thus the all-label ceiling is available for every genuine heat nome below
one, with no cutoff field or search oracle.
-/

/-- Explicit all-label cutoff obtained from the constructive `q^n → 0`
modulus at target `1/4`. -/
def explicitLabelCutoff (nome : Q') : Nat :=
  HKConvGen.powBaseCutoff nome (Q'.mkPos 1 4 (by decide)) + 1

/-- The explicit cutoff is a positive label index. -/
theorem explicitLabelCutoff_pos (nome : Q') :
    1 ≤ explicitLabelCutoff nome := by
  unfold explicitLabelCutoff
  omega

/-- **The explicit cutoff has discarded ratio at most `1/2`.** -/
theorem explicitLabelCutoff_ratio_le_half
    {nome : Q'} (hnome0 : (0 : Q') < nome) (hnome1 : nome < 1) :
    discardedRatio nome (explicitLabelCutoff nome)
      ≤ Q'.mkPos 1 2 (by decide) := by
  let n₀ := HKConvGen.powBaseCutoff nome (Q'.mkPos 1 4 (by decide))
  have hquarter :
      nome ^ n₀ ≤ Q'.mkPos 1 4 (by decide) := by
    exact HKConvGen.pow_base_le_cutoff hnome0 hnome1 (by decide)
  have hexponent :
      n₀ ≤ 2 * (explicitLabelCutoff nome + 1) := by
    unfold explicitLabelCutoff
    dsimp [n₀]
    omega
  have hpower :
      nome ^ (2 * (explicitLabelCutoff nome + 1))
        ≤ nome ^ n₀ := by
    exact HKConvGen.pow_base_antitone
      (Q'.le_of_lt hnome0) (Q'.le_of_lt hnome1) hexponent
  have hscaled :
      Q'.ofNat 2 * nome ^ (2 * (explicitLabelCutoff nome + 1))
        ≤ Q'.ofNat 2 * Q'.mkPos 1 4 (by decide) := by
    exact Q'.mul_le_mul_of_nonneg_left _ _ _
      (Q'.le_trans' _ _ _ hpower hquarter) (by decide)
  exact Q'.le_trans' _ _ _ hscaled (Q'.le_of_eqv (by decide))

/-- **Constructed all-label ceiling for every heat nome `0 < nome < 1`.**
Every finite Peter--Weyl partial sum is bounded at the explicit
spacing-dependent cutoff. -/
theorem allLabelPartial_le_explicitCeiling
    {nome : Q'} (hnome0 : (0 : Q') < nome) (hnome1 : nome < 1) :
    ∀ K, finSum (chanCoeff nome) K
      ≤ onePlaquetteCeiling nome (explicitLabelCutoff nome) := by
  exact allLabelPartial_le_ceiling
    (Q'.le_of_lt hnome0)
    (Q'.le_trans' _ _ _ (Q'.le_of_lt hnome1) (Q'.le_refl' 1))
    (explicitLabelCutoff nome)
    (explicitLabelCutoff_pos nome)
    (explicitLabelCutoff_ratio_le_half hnome0 hnome1)

/-! ### The same cutoff closes the all-label Hilbert--Schmidt completion

The coefficient-tail and Hilbert--Schmidt developments use the same
Casimir ratio.  Thus the spacing-dependent cutoff constructed above supplies
the cutoff data required by the genuine Haar--`L²` completion, for every
heat nome strictly between zero and one.
-/

/-- The explicit label cutoff canonically supplies the constructive
all-label Hilbert--Schmidt cutoff data. -/
def explicitHeatChannelHSCutoff
    (nome : Q') (hnome0 : (0 : Q') < nome) (hnome1 : nome < 1) :
    HeatChannelHSCutoff where
  q := nome
  q_pos := hnome0
  q_le_one := Q'.le_of_lt hnome1
  cutoff := explicitLabelCutoff nome
  cutoff_one := explicitLabelCutoff_pos nome
  ratio_lt_one := by
    have hhalf :
        channelRatio nome (explicitLabelCutoff nome)
          ≤ Q'.mkPos 1 2 (by decide) := by
      simpa [channelRatio, discardedRatio] using
        explicitLabelCutoff_ratio_le_half hnome0 hnome1
    exact Q'.lt_of_le_of_lt hhalf (by decide)

/-- **Spacing-dependent all-label Haar--Hilbert--Schmidt convergence.**
For every genuine heat nome `0 < nome < 1`, the finite Peter--Weyl
Haar-`L²` squares converge constructively to the infinite
Hilbert--Schmidt square selected by the explicit cutoff. -/
theorem explicit_heatHaarPartialHSSq_converges
    (nome : Q') (hnome0 : (0 : Q') < nome) (hnome1 : nome < 1) :
    CReal.ConvergesTo
      (heatHaarPartialHSSq
        (explicitHeatChannelHSCutoff nome hnome0 hnome1))
      (heatChannelHSSq
        (explicitHeatChannelHSCutoff nome hnome0 hnome1)) :=
  heatHaarPartialHSSq_converges
    (explicitHeatChannelHSCutoff nome hnome0 hnome1)

/-! ## 2. Type-level moving-cutoff and five-holonomy certificates -/

/-- The base used for the rational bit budget. -/
def four : Q' := Q'.ofNat 4

/-- The target nonlinear spectral ratio. -/
def quarter : Q' := Q'.mkPos 1 4 (by decide)

/-- `48` five-holonomy factors followed by the fourth-power Perron buffer:
`48 * 4 = 192`. -/
def bufferExponent (bits : Nat) : Nat := bits * (48 * 4)

/-- The geometric exponent is literally `192 * bits`. -/
theorem bufferExponent_eq_192_mul (bits : Nat) :
    bufferExponent bits = 192 * bits := by
  unfold bufferExponent
  omega

/-- A constructive moving-cutoff certificate.  The only nontrivial numerical
check is the exact rational comparison `ceiling_le_cap`; the all-label tail
behind the ceiling is proved above. -/
structure AllLabelCutoffCertificate : Type where
  nome : Q'
  cutoff : Nat
  lower : Q'
  bits : Nat
  nome_nonneg : (0 : Q') ≤ nome
  nome_le_one : nome ≤ 1
  cutoff_pos : 1 ≤ cutoff
  ratio_le_half :
    discardedRatio nome cutoff ≤ Q'.mkPos 1 2 (by decide)
  lower_pos : (0 : Q') < lower
  ceiling_le_cap :
    onePlaquetteCeiling nome cutoff ≤ four ^ bits * lower

/-- The full all-label coefficient bound supplied by a cutoff certificate. -/
theorem allLabel_le_cap (D : AllLabelCutoffCertificate) :
    ∀ K, finSum (chanCoeff D.nome) K ≤ four ^ D.bits * D.lower := by
  intro K
  exact Q'.le_trans' _ _ _
    (allLabelPartial_le_ceiling D.nome_nonneg D.nome_le_one
      D.cutoff D.cutoff_pos D.ratio_le_half K)
    D.ceiling_le_cap

/-- The geometric part of the BF4 five-holonomy comparison.

`kernel_from_allLabel` explicitly consumes the proved all-label bound and
contributes the 48 local factors.  `perron_fourfold` is the two-sided Perron
buffer squared, hence the fourth power of the kernel ratio. -/
structure FiveHolonomyGeometry (D : AllLabelCutoffCertificate) : Type where
  kernelRatio : Q'
  cSsq : Q'
  kernelRatio_nonneg : (0 : Q') ≤ kernelRatio
  cSsq_nonneg : (0 : Q') ≤ cSsq
  kernel_from_allLabel :
    (∀ K, finSum (chanCoeff D.nome) K ≤ four ^ D.bits * D.lower) →
      kernelRatio ≤ (four ^ D.bits) ^ 48
  perron_fourfold : cSsq ≤ kernelRatio ^ 4

/-- The remaining nonlinear spectral certificate.  In the intended
application `qS` is the Perron spectral ratio `q_s`, not the heat-kernel
nome. -/
structure NonlinearSpectralCertificate (bits : Nat) : Type where
  qS : Q'
  m : Nat
  qS_nonneg : (0 : Q') ≤ qS
  qS_le_quarter : qS ≤ quarter
  moving_depth : 192 * bits + 1 ≤ m - 2

/-! ## 3. Exact power arithmetic and the strict cutoff theorem -/

/-- Base monotonicity of rational powers. -/
theorem pow_base_mono (a b : Q') (ha : (0 : Q') ≤ a) (hab : a ≤ b) :
    ∀ n : Nat, a ^ n ≤ b ^ n
  | 0 => Q'.le_refl' 1
  | n + 1 => by
      have hb : (0 : Q') ≤ b := Q'.le_trans' _ _ _ ha hab
      exact Q'.le_trans' _ _ _
        (Q'.mul_le_mul_of_nonneg_right _ _ _ hab (Q'.pow_nonneg a ha n))
        (Q'.mul_le_mul_of_nonneg_left _ _ _ (pow_base_mono a b ha hab n) hb)

/-- `(x^a)^b = x^(a*b)` up to rational semantic equivalence. -/
theorem pow_mul_eqv (x : Q') (a : Nat) :
    ∀ b, ((x ^ a) ^ b).eqv (x ^ (a * b))
  | 0 => by
      rw [Nat.mul_zero]
      exact Q'.eqv_refl 1
  | b + 1 => by
      have ih := pow_mul_eqv x a b
      rw [Nat.mul_succ]
      have hcomm : a * b + a = a + a * b := by omega
      rw [hcomm]
      exact Q'.eqv_trans _ _ _
        (Q'.mul_eqv_congr_left (x ^ a) _ _ ih)
        (Q'.eqv_symm (Q'.pow_add_eqv x a (a * b)))

/-- The 48-factor/fourfold geometry gives the exact moving cap
`C_s^2 <= 4^(192 B)`. -/
theorem cSsq_le_movingCap
    (D : AllLabelCutoffCertificate) (G : FiveHolonomyGeometry D) :
    G.cSsq ≤ four ^ bufferExponent D.bits := by
  have hkernel : G.kernelRatio ≤ (four ^ D.bits) ^ 48 :=
    G.kernel_from_allLabel (allLabel_le_cap D)
  have hpow :
      G.kernelRatio ^ 4 ≤ ((four ^ D.bits) ^ 48) ^ 4 :=
    pow_base_mono G.kernelRatio ((four ^ D.bits) ^ 48)
      G.kernelRatio_nonneg hkernel 4
  have hnested :
      (((four ^ D.bits) ^ 48) ^ 4).eqv
        (four ^ bufferExponent D.bits) := by
    exact Q'.eqv_trans _ _ _
      (pow_mul_eqv (four ^ D.bits) 48 4)
      (pow_mul_eqv four D.bits (48 * 4))
  exact Q'.le_trans' _ _ _
    (Q'.le_trans' _ _ _ G.perron_fourfold hpow)
    (Q'.le_of_eqv hnested)

/-- `4*q <= 1` whenever `q <= 1/4`. -/
theorem four_mul_le_one {q : Q'} (hq : q ≤ quarter) :
    four * q ≤ 1 := by
  exact Q'.le_trans' _ _ _
    (Q'.mul_le_mul_of_nonneg_left _ _ _ hq (by decide))
    (Q'.le_of_eqv (by decide))

/-- Exact cancellation budget:
`4^K q^(K+1) <= 1/4` for `0 <= q <= 1/4`. -/
theorem fourPow_mul_qSucc_le_quarter
    {q : Q'} (hq0 : (0 : Q') ≤ q) (hqQuarter : q ≤ quarter) :
    ∀ K, four ^ K * q ^ (K + 1) ≤ quarter
  | 0 => by
      have he : ((1 : Q') * (q * 1)).eqv q :=
        Q'.eqv_trans _ _ _
          (Q'.one_mul_eqv (q * 1))
          (Q'.mul_one_eqv q)
      exact Q'.le_trans' _ _ _ (Q'.le_of_eqv he) hqQuarter
  | K + 1 => by
      have ih := fourPow_mul_qSucc_le_quarter hq0 hqQuarter K
      have hold0 :
          (0 : Q') ≤ four ^ K * q ^ (K + 1) :=
        Q'.mul_nonneg _ _
          (Q'.pow_nonneg four (by decide) K)
          (Q'.pow_nonneg q hq0 (K + 1))
      have hfirst :
          (four * q) * (four ^ K * q ^ (K + 1))
            ≤ (1 : Q') * (four ^ K * q ^ (K + 1)) :=
        Q'.mul_le_mul_of_nonneg_right _ _ _
          (four_mul_le_one hqQuarter) hold0
      have hsecond :
          (1 : Q') * (four ^ K * q ^ (K + 1))
            ≤ (1 : Q') * quarter :=
        Q'.mul_le_mul_of_nonneg_left _ _ _ ih (by decide)
      have hreorder :
          ((four * four ^ K) * (q * q ^ (K + 1))).eqv
            ((four * q) * (four ^ K * q ^ (K + 1))) :=
        YMGap.Constructive.SU3CharFactor.mul_interchange_eqv
          four (four ^ K) q (q ^ (K + 1))
      exact Q'.le_trans' _ _ _
        (Q'.le_of_eqv hreorder)
        (Q'.le_trans' _ _ _
          (Q'.le_trans' _ _ _ hfirst hsecond)
          (Q'.le_of_eqv (Q'.one_mul_eqv quarter)))

/-- If the available exponent is at least `K+1`, the same budget holds. -/
theorem fourPow_mul_qPow_le_quarter
    {q : Q'} (hq0 : (0 : Q') ≤ q) (hqQuarter : q ≤ quarter)
    (K r : Nat) (hKr : K + 1 ≤ r) :
    four ^ K * q ^ r ≤ quarter := by
  have hqOne : q ≤ (1 : Q') :=
    Q'.le_trans' _ _ _ hqQuarter (by decide)
  have hpow : q ^ r ≤ q ^ (K + 1) :=
    HKConvGen.pow_base_antitone hq0 hqOne hKr
  exact Q'.le_trans' _ _ _
    (Q'.mul_le_mul_of_nonneg_left _ _ _ hpow
      (Q'.pow_nonneg four (by decide) K))
    (fourPow_mul_qSucc_le_quarter hq0 hqQuarter K)

/-- **Quantitative BF4 cutoff theorem.**

Under the explicitly certified coefficient tail, 48-factor geometry,
fourfold Perron buffer, nonlinear quarter-ratio, and moving-depth inequality,
the desired strict contraction follows:

`C_s^2 * q_s^(m-2) < 1`.
-/
theorem perron_cutoff_strict
    (D : AllLabelCutoffCertificate)
    (G : FiveHolonomyGeometry D)
    (S : NonlinearSpectralCertificate D.bits) :
    G.cSsq * S.qS ^ (S.m - 2) < 1 := by
  have hcap := cSsq_le_movingCap D G
  have hqpow0 : (0 : Q') ≤ S.qS ^ (S.m - 2) :=
    Q'.pow_nonneg S.qS S.qS_nonneg _
  have hproduct :
      G.cSsq * S.qS ^ (S.m - 2)
        ≤ four ^ bufferExponent D.bits * S.qS ^ (S.m - 2) :=
    Q'.mul_le_mul_of_nonneg_right _ _ _ hcap hqpow0
  have hquarter :
      four ^ bufferExponent D.bits * S.qS ^ (S.m - 2) ≤ quarter :=
    fourPow_mul_qPow_le_quarter S.qS_nonneg S.qS_le_quarter
      (bufferExponent D.bits) (S.m - 2) (by
        rw [bufferExponent_eq_192_mul]
        exact S.moving_depth)
  exact Q'.lt_of_le_of_lt
    (Q'.le_trans' _ _ _ hproduct hquarter)
    (by decide)

end YMGap.Continuum.FiveHolonomyPerronCutoff

/-! ## Axiom-dependency gates -/

#print axioms YMGap.Continuum.FiveHolonomyPerronCutoff.geometricPartial_le_two
#print axioms YMGap.Continuum.FiveHolonomyPerronCutoff.discardedPartial_le_twoLead
#print axioms YMGap.Continuum.FiveHolonomyPerronCutoff.allLabelPartial_le_ceiling
#print axioms YMGap.Continuum.FiveHolonomyPerronCutoff.explicitLabelCutoff_ratio_le_half
#print axioms YMGap.Continuum.FiveHolonomyPerronCutoff.allLabelPartial_le_explicitCeiling
#print axioms YMGap.Continuum.FiveHolonomyPerronCutoff.explicitHeatChannelHSCutoff
#print axioms YMGap.Continuum.FiveHolonomyPerronCutoff.explicit_heatHaarPartialHSSq_converges
#print axioms YMGap.Continuum.FiveHolonomyPerronCutoff.allLabel_le_cap
#print axioms YMGap.Continuum.FiveHolonomyPerronCutoff.bufferExponent_eq_192_mul
#print axioms YMGap.Continuum.FiveHolonomyPerronCutoff.cSsq_le_movingCap
#print axioms YMGap.Continuum.FiveHolonomyPerronCutoff.fourPow_mul_qPow_le_quarter
#print axioms YMGap.Continuum.FiveHolonomyPerronCutoff.perron_cutoff_strict
