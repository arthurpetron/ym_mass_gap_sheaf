/-
# Infinite SU(2) heat-channel Hilbert--Schmidt completion

This module continues `SU2HaarL2HilbertSchmidt` from fixed character rank to
the genuine all-label SU(2) heat-channel coefficient sequence

  a_j(q) = (2j+1) q^{j(j+1)}.

The input is a constructive cutoff certificate: `0 < q ≤ 1`, a cutoff
`N ≥ 1`, and the proved channel ratio

  rho = 2 q^{2(N+1)} < 1.

`TruncationTailChannelBound.chanCoeff_geoDom` then gives
`a_{N+l} ≤ a_N rho^l`.  We square that proved inequality, obtaining the
quantitative Hilbert--Schmidt tail

  Σ_{i<d} a_{N+m+i}²
    ≤ (a_N² rho^{2m}) / (1-rho²).

The geometric CReal completion engine constructs the infinite squared norm,
and the finite Haar-L2/Parseval layer proves that the actual finite character
packet norms converge to it.

Honest scope: this is the diagonal SU(2) heat channel in its orthonormal
character basis.  It does not assert BCH stability, Haar-Jacobian stability,
or Hilbert--Schmidt convergence for the nonlinear BF4 five-holonomy
rescaling kernel.

# Axiom gate

All data and witnesses are in `Type`.  No `Classical.*`, `Real`,
`native_decide`, choice, custom axiom, or placeholder is used.
-/

import YMGap.Continuum.SU2HaarL2HilbertSchmidt
import YMGap.Continuum.TruncationTailChannelBound

namespace YMGap.Continuum.SU2HeatChannelHilbertSchmidtCompletion

open YMGap.Constructive
open YMGap.Constructive.RationalTail
open YMGap.Continuum
open YMGap.Continuum.HKConvGen
open YMGap.Continuum.TruncationTailChannelBound
open YMGap.Continuum.SU2HaarL2HilbertSchmidt

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. Constructive heat-channel cutoff data -/

/-- The super-geometric comparison ratio after character cutoff `N`. -/
def channelRatio (q : Q') (N : Nat) : Q' :=
  Q'.ofNat 2 * q ^ (2 * (N + 1))

/-- Type-level data sufficient to sum the squared all-label heat channel. -/
structure HeatChannelHSCutoff : Type where
  q : Q'
  q_pos : (0 : Q') < q
  q_le_one : q ≤ (1 : Q')
  cutoff : Nat
  cutoff_one : 1 ≤ cutoff
  ratio_lt_one : channelRatio q cutoff < (1 : Q')

/-- The squared channel coefficient, the Hilbert--Schmidt summand in the
orthonormal character basis. -/
def channelCoeffSq (q : Q') (j : Nat) : Q' :=
  chanCoeff q j * chanCoeff q j

/-- Exact finite all-label Hilbert--Schmidt square. -/
def heatHSPartial (q : Q') (M : Nat) : Q' :=
  finSum (channelCoeffSq q) M

/-- Finite sums of nonnegative rational terms are nonnegative. -/
theorem finSum_nonneg_local (f : Nat → Q')
    (hf : ∀ i, (0 : Q') ≤ f i) :
    ∀ M, (0 : Q') ≤ finSum f M
  | 0 => Q'.le_refl' 0
  | M + 1 => Q'.zero_le_add _ _
      (finSum_nonneg_local f hf M) (hf M)

/-- Every finite heat-channel HS square is nonnegative. -/
theorem heatHSPartial_nonneg (D : HeatChannelHSCutoff) (M : Nat) :
    (0 : Q') ≤ heatHSPartial D.q M :=
  finSum_nonneg_local _ (fun j =>
    Q'.mul_nonneg _ _
      (chanCoeff_nonneg (Q'.le_of_lt D.q_pos) j)
      (chanCoeff_nonneg (Q'.le_of_lt D.q_pos) j)) M

/-- First squared coefficient in the discarded tail. -/
def leadSq (D : HeatChannelHSCutoff) : Q' :=
  channelCoeffSq D.q D.cutoff

/-- Squared geometric ratio for the Hilbert--Schmidt tail. -/
def ratioSq (D : HeatChannelHSCutoff) : Q' :=
  channelRatio D.q D.cutoff * channelRatio D.q D.cutoff

theorem channelRatio_pos (D : HeatChannelHSCutoff) :
    (0 : Q') < channelRatio D.q D.cutoff := by
  exact Q'.mul_pos (by simpa using Q'.ofNat_succ_pos 1)
    (HKPos.pow_pos D.q_pos _)

theorem channelRatio_nonneg (D : HeatChannelHSCutoff) :
    (0 : Q') ≤ channelRatio D.q D.cutoff :=
  Q'.le_of_lt (channelRatio_pos D)

theorem ratioSq_pos (D : HeatChannelHSCutoff) :
    (0 : Q') < ratioSq D :=
  Q'.mul_pos (channelRatio_pos D) (channelRatio_pos D)

theorem ratioSq_lt_one (D : HeatChannelHSCutoff) :
    ratioSq D < (1 : Q') := by
  have hmul :
      channelRatio D.q D.cutoff * channelRatio D.q D.cutoff
        ≤ (1 : Q') * channelRatio D.q D.cutoff :=
    Q'.mul_le_mul_of_nonneg_right
      (channelRatio D.q D.cutoff) 1 (channelRatio D.q D.cutoff)
      (Q'.le_of_lt D.ratio_lt_one) (channelRatio_nonneg D)
  have hone :
      (1 : Q') * channelRatio D.q D.cutoff
        ≤ channelRatio D.q D.cutoff :=
    Q'.le_of_eqv (Q'.one_mul_eqv (channelRatio D.q D.cutoff))
  exact Q'.lt_of_le_of_lt
    (Q'.le_trans' _ _ _ hmul hone) D.ratio_lt_one

theorem channelCoeff_pos (D : HeatChannelHSCutoff) (j : Nat) :
    (0 : Q') < chanCoeff D.q j := by
  exact Q'.mul_pos (by simpa using Q'.ofNat_succ_pos (2 * j))
    (HKPos.pow_pos D.q_pos _)

theorem leadSq_pos (D : HeatChannelHSCutoff) :
    (0 : Q') < leadSq D :=
  Q'.mul_pos (channelCoeff_pos D D.cutoff)
    (channelCoeff_pos D D.cutoff)

theorem leadSq_nonneg (D : HeatChannelHSCutoff) :
    (0 : Q') ≤ leadSq D :=
  Q'.le_of_lt (leadSq_pos D)

/-! ## 2. Squaring the proved super-geometric channel domination -/

/-- Four-factor regrouping `(A B)(C D) ≈ (A C)(B D)`. -/
theorem mul_four_regroup (A B C D : Q') :
    ((A * B) * (C * D)) ≈ ((A * C) * (B * D)) := by
  refine Q'.eqv_trans _ _ _ (Q'.mul_assoc_eqv A B (C * D)) ?_
  refine Q'.eqv_trans _ _ _ ?_
    (Q'.eqv_symm (Q'.mul_assoc_eqv A C (B * D)))
  refine Q'.mul_eqv_congr_left A _ _ ?_
  refine Q'.eqv_trans _ _ _
    (Q'.eqv_symm (Q'.mul_assoc_eqv B C D)) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_right _ _ D (Q'.mul_comm_eqv B C)) ?_
  exact Q'.mul_assoc_eqv C B D

/-- The power of a squared ratio is the square of the power. -/
theorem pow_mul_self (r : Q') :
    ∀ l : Nat, (r * r) ^ l ≈ r ^ l * r ^ l
  | 0 => Q'.eqv_symm (Q'.one_mul_eqv 1)
  | l + 1 => by
      show (r * r) * (r * r) ^ l ≈
        (r * r ^ l) * (r * r ^ l)
      refine Q'.eqv_trans _ _ _
        (Q'.mul_eqv_congr_left (r * r) _ _ (pow_mul_self r l)) ?_
      exact mul_four_regroup r r (r ^ l) (r ^ l)

/-- **Squared super-geometric domination.**
`a_{N+l}² ≤ a_N² (rho²)^l`, derived by squaring
`chanCoeff_geoDom`; it is not an additional tail assumption. -/
theorem channelCoeffSq_geoDom (D : HeatChannelHSCutoff) (l : Nat) :
    channelCoeffSq D.q (D.cutoff + l)
      ≤ leadSq D * ratioSq D ^ l := by
  have hdom :
      chanCoeff D.q (D.cutoff + l)
        ≤ chanCoeff D.q D.cutoff *
          channelRatio D.q D.cutoff ^ l := by
    exact chanCoeff_geoDom (Q'.le_of_lt D.q_pos) D.q_le_one
      D.cutoff D.cutoff_one l
  have hterm0 :
      (0 : Q') ≤ chanCoeff D.q (D.cutoff + l) :=
    chanCoeff_nonneg (Q'.le_of_lt D.q_pos) _
  have hmajor0 :
      (0 : Q') ≤ chanCoeff D.q D.cutoff *
          channelRatio D.q D.cutoff ^ l :=
    Q'.mul_nonneg _ _
      (chanCoeff_nonneg (Q'.le_of_lt D.q_pos) _)
      (Q'.pow_nonneg _ (channelRatio_nonneg D) _)
  have hsquare :
      chanCoeff D.q (D.cutoff + l) *
          chanCoeff D.q (D.cutoff + l)
        ≤ (chanCoeff D.q D.cutoff *
            channelRatio D.q D.cutoff ^ l) *
          (chanCoeff D.q D.cutoff *
            channelRatio D.q D.cutoff ^ l) := by
    have h1 :=
      Q'.mul_le_mul_of_nonneg_right _ _ _
        hdom hterm0
    have h2 :=
      Q'.mul_le_mul_of_nonneg_left _ _ _
        hdom hmajor0
    exact Q'.le_trans' _ _ _ h1 h2
  refine Q'.le_trans' _ _ _ hsquare (Q'.le_of_eqv ?_)
  refine Q'.eqv_trans _ _ _
    (mul_four_regroup (chanCoeff D.q D.cutoff)
      (channelRatio D.q D.cutoff ^ l)
      (chanCoeff D.q D.cutoff)
      (channelRatio D.q D.cutoff ^ l)) ?_
  exact Q'.mul_eqv_congr_left
    (chanCoeff D.q D.cutoff * chanCoeff D.q D.cutoff) _ _
    (Q'.eqv_symm (pow_mul_self (channelRatio D.q D.cutoff) l))

/-! ## 3. Quantitative squared-tail bound and CReal tail -/

/-- Squared discarded-channel partial sum beginning at the certified cutoff. -/
def squaredTailPartial (D : HeatChannelHSCutoff) (M : Nat) : Q' :=
  finSum (fun l => channelCoeffSq D.q (D.cutoff + l)) M

/-- **Quantitative squared tail after `m` discarded labels.**
Every finite tail window is bounded by
`(a_N² (rho²)^m)/(1-rho²)`. -/
theorem squaredTailWindow_le (D : HeatChannelHSCutoff) (m d : Nat) :
    finSum
      (fun i => channelCoeffSq D.q (D.cutoff + (m + i))) d
      ≤ geoTailBase (leadSq D) (ratioSq D) m := by
  have hterm :
      finSum
        (fun i => channelCoeffSq D.q (D.cutoff + (m + i))) d
        ≤ finSum
          (fun i => geoIncrBase (leadSq D) (ratioSq D) (m + i)) d :=
    TruncationTailChannelBound.finSum_le_termwise _ _
      (fun i => by
        unfold geoIncrBase
        exact channelCoeffSq_geoDom D (m + i)) d
  exact Q'.le_trans' _ _ _ hterm
    (geoTailBase_series_le (leadSq_nonneg D)
      (ratioSq_pos D) (ratioSq_lt_one D) m d)

theorem squaredTail_hup (D : HeatChannelHSCutoff) (l : Nat) :
    squaredTailPartial D (l + 1)
      ≤ squaredTailPartial D l +
        geoIncrBase (leadSq D) (ratioSq D) l := by
  show squaredTailPartial D l +
      channelCoeffSq D.q (D.cutoff + l)
    ≤ squaredTailPartial D l +
      geoIncrBase (leadSq D) (ratioSq D) l
  exact Q'.add_le_add_left _ _ _
    (channelCoeffSq_geoDom D l)

theorem squaredTail_hlo (D : HeatChannelHSCutoff) (l : Nat) :
    squaredTailPartial D l
      ≤ squaredTailPartial D (l + 1) +
        geoIncrBase (leadSq D) (ratioSq D) l := by
  have hterm0 :
      (0 : Q') ≤ channelCoeffSq D.q (D.cutoff + l) :=
    Q'.mul_nonneg _ _
      (chanCoeff_nonneg (Q'.le_of_lt D.q_pos) _)
      (chanCoeff_nonneg (Q'.le_of_lt D.q_pos) _)
  have hmono :
      squaredTailPartial D l ≤ squaredTailPartial D (l + 1) := by
    exact Q'.add_le_self_of_nonneg _ _ hterm0
  exact Q'.le_trans' _ _ _ hmono
    (Q'.add_le_self_of_nonneg _ _
      (geoIncrBase_nonneg (leadSq_nonneg D)
        (Q'.le_of_lt (ratioSq_pos D)) l))

/-- Explicit rescaling modulus consumed by the geometric CReal engine. -/
theorem squaredTail_modulus (D : HeatChannelHSCutoff) :
    ∀ ε : Q', (0 : Q') < ε →
      ∃ δ : Q', (0 : Q') < δ ∧
        (leadSq D *
          HKConv.divPos 1 (1 + (-ratioSq D))) * δ ≤ ε := by
  intro ε hε
  have hLeadNum : 0 < (leadSq D).num :=
    CReal.num_pos_of_pos (leadSq_pos D)
  have hHNum :
      0 < (HKConv.divPos 1 (1 + (-ratioSq D))).num :=
    HKConv.divPos_num_pos (by decide)
  have hScaleNum :
      0 < (leadSq D *
        HKConv.divPos 1 (1 + (-ratioSq D))).num := by
    show 0 < (leadSq D).num *
      (HKConv.divPos 1 (1 + (-ratioSq D))).num
    exact Int.mul_pos hLeadNum hHNum
  refine
    ⟨HKConv.divPos ε
        (leadSq D * HKConv.divPos 1 (1 + (-ratioSq D))),
      HKConv.divPos_pos (CReal.num_pos_of_pos hε), ?_⟩
  refine Q'.le_of_eqv ?_
  refine Q'.eqv_trans _ _ _
    (Q'.mul_comm_eqv
      (leadSq D * HKConv.divPos 1 (1 + (-ratioSq D)))
      (HKConv.divPos ε
        (leadSq D * HKConv.divPos 1 (1 + (-ratioSq D))))) ?_
  exact HKConv.divPos_mul_eqv hScaleNum

/-- The genuine CReal sum of all squared coefficients in the discarded tail. -/
def squaredTailCR (D : HeatChannelHSCutoff) : CReal :=
  crealOfGeoIncrementBase
    (squaredTailPartial D) (leadSq D) (ratioSq D)
    (leadSq_nonneg D) (ratioSq_pos D) (ratioSq_lt_one D)
    (squaredTail_hup D) (squaredTail_hlo D) (squaredTail_modulus D)

@[simp] theorem squaredTailCR_approx (D : HeatChannelHSCutoff) (M : Nat) :
    (squaredTailCR D).approx M = squaredTailPartial D M := rfl

/-- The infinite squared tail is bounded by the explicit geometric budget
`a_N²/(1-rho²)`. -/
theorem squaredTailCR_leRat (D : HeatChannelHSCutoff) :
    CReal.leRat (squaredTailCR D)
      (geoTailBase (leadSq D) (ratioSq D) 0) := by
  apply CReal.leRat_of_eventually
  refine ⟨0, fun M _ => ?_⟩
  rw [squaredTailCR_approx]
  simpa [squaredTailPartial] using squaredTailWindow_le D 0 M

/-! ## 4. Full all-label completion and convergence of Haar-HS partial sums -/

/-- The exact finite head before the certified geometric tail. -/
def squaredHead (D : HeatChannelHSCutoff) : Q' :=
  heatHSPartial D.q D.cutoff

/-- **Infinite all-label heat-channel Hilbert--Schmidt square.**
It is the exact finite head plus the genuinely constructed CReal squared tail. -/
def heatChannelHSSq (D : HeatChannelHSCutoff) : CReal :=
  CReal.add (CReal.ofQ' (squaredHead D)) (squaredTailCR D)

/-- Every approximation of the infinite all-label HS square is nonnegative. -/
theorem heatChannelHSSq_approx_nonneg
    (D : HeatChannelHSCutoff) (p : Nat) :
    (0 : Q') ≤ (heatChannelHSSq D).approx p := by
  show (0 : Q') ≤ squaredHead D + squaredTailPartial D p
  exact Q'.zero_le_add _ _
    (heatHSPartial_nonneg D D.cutoff)
    (finSum_nonneg_local _ (fun l =>
      Q'.mul_nonneg _ _
        (chanCoeff_nonneg (Q'.le_of_lt D.q_pos) (D.cutoff + l))
        (chanCoeff_nonneg (Q'.le_of_lt D.q_pos) (D.cutoff + l))) p)

/-- The completed all-label heat-channel HS square is nonnegative as a
constructive real. -/
theorem heatChannelHSSq_nonneg (D : HeatChannelHSCutoff) :
    ExpPos.geRat (heatChannelHSSq D) 0 :=
  ExpPos.geRat_of_eventually
    ⟨0, fun p _ => heatChannelHSSq_approx_nonneg D p⟩

/-- Split a finite sum into its head and shifted tail. -/
theorem finSum_split (f : Nat → Q') (N : Nat) :
    ∀ M, finSum f (N + M) ≈
      finSum f N + finSum (fun i => f (N + i)) M
  | 0 => by
      show finSum f N ≈ finSum f N + (0 : Q')
      exact Q'.eqv_of_eq (Q'.add_zero' _).symm
  | M + 1 => by
      show finSum f (N + M) + f (N + M) ≈
        finSum f N +
          (finSum (fun i => f (N + i)) M + f (N + M))
      refine Q'.eqv_trans _ _ _
        (Q'.add_eqv_congr_right _ _ (f (N + M))
          (finSum_split f N M)) ?_
      exact Q'.add_assoc_eqv (finSum f N)
        (finSum (fun i => f (N + i)) M) (f (N + M))

/-- The shifted finite rational HS square is termwise the approximation
sequence of the constructed all-label completion. -/
theorem shiftedHeatHS_equiv_completionApprox
    (D : HeatChannelHSCutoff) (M : Nat) :
    CReal.Equiv
      (CReal.ofQ' (heatHSPartial D.q (D.cutoff + M)))
      (CReal.ofQ' ((heatChannelHSSq D).approx M)) := by
  refine SumOfSquares.Equiv_of_approx_eqv (fun p => ?_)
  show heatHSPartial D.q (D.cutoff + M) ≈
    squaredHead D + squaredTailPartial D M
  exact finSum_split (channelCoeffSq D.q) D.cutoff M

/-- The cofinal sequence of finite coefficient HS squares converges to the
constructed all-label square. -/
theorem shiftedHeatHSPartial_converges (D : HeatChannelHSCutoff) :
    CReal.ConvergesTo
      (fun M => CReal.ofQ' (heatHSPartial D.q (D.cutoff + M)))
      (heatChannelHSSq D) := by
  exact ChebOrthoMatrix.convergesTo_congr_seq
    (fun M => CReal.Equiv.symm
      (shiftedHeatHS_equiv_completionApprox D M))
    (CReal.convergesTo_self (heatChannelHSSq D))

/-- If a fixed shift of a sequence converges, the original sequence converges
to the same limit.  This is constructive cofinal bookkeeping. -/
theorem convergesTo_of_fixedShift
    {s : Nat → CReal} {L : CReal} (K : Nat)
    (h : CReal.ConvergesTo (fun M => s (K + M)) L) :
    CReal.ConvergesTo s L := by
  intro ε hε
  obtain ⟨Nstage, hstage⟩ := h ε hε
  refine ⟨K + Nstage, fun M hM => ?_⟩
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hM
  have hNd : Nstage ≤ Nstage + d := Nat.le_add_right _ _
  simpa [Nat.add_assoc] using hstage (Nstage + d) hNd

/-- **All finite coefficient Hilbert--Schmidt squares converge** to the
constructed infinite all-label square. -/
theorem heatHSPartial_converges (D : HeatChannelHSCutoff) :
    CReal.ConvergesTo
      (fun M => CReal.ofQ' (heatHSPartial D.q M))
      (heatChannelHSSq D) := by
  apply convergesTo_of_fixedShift D.cutoff
  simpa [Nat.add_comm] using shiftedHeatHSPartial_converges D

/-- The finite Haar-L2 square of the heat character packet. -/
def heatHaarPartialHSSq (D : HeatChannelHSCutoff) (M : Nat) : CReal :=
  haarL2Pairing (chanCoeff D.q) (chanCoeff D.q) M

/-- Each finite Haar-L2 square is exactly its coefficient sum of squares. -/
theorem heatHaarPartialHSSq_equiv_coeff
    (D : HeatChannelHSCutoff) (M : Nat) :
    CReal.Equiv (heatHaarPartialHSSq D M)
      (CReal.ofQ' (heatHSPartial D.q M)) := by
  refine SumOfSquares.Equiv_of_approx_eqv (fun p => ?_)
  unfold heatHaarPartialHSSq haarL2Pairing heatHSPartial channelCoeffSq
  rw [CReal.csum_approx]
  exact Q'.eqv_refl _

/-- **Infinite all-label Haar--Hilbert--Schmidt convergence.**
The finite Haar-L2/Parseval squares of the genuine SU(2) heat-channel
coefficients converge to the constructed CReal all-label HS square. -/
theorem heatHaarPartialHSSq_converges (D : HeatChannelHSCutoff) :
    CReal.ConvergesTo (heatHaarPartialHSSq D) (heatChannelHSSq D) := by
  exact ChebOrthoMatrix.convergesTo_congr_seq
    (fun M => CReal.Equiv.symm
      (heatHaarPartialHSSq_equiv_coeff D M))
    (heatHSPartial_converges D)

/-- At each fixed character cutoff, the genuine normalized midpoint Haar
Riemann sums converge to the heat-channel partial HS square. -/
theorem heatHaarRiemann_converges
    (D : HeatChannelHSCutoff) (M : Nat) :
    CReal.ConvergesTo
      (packetRiemannPairing (chanCoeff D.q) (chanCoeff D.q) M)
      (heatHaarPartialHSSq D M) :=
  packetRiemannPairing_converges
    (chanCoeff D.q) (chanCoeff D.q) M

/-! ## 5. Concrete non-vacuity: the existing pilot cutoff -/

/-- The repository's exact `q=1/2`, `N=4`, `rho=1/512` pilot inhabits the
generic all-label Hilbert--Schmidt cutoff data. -/
def pilotHeatChannelHSCutoff : HeatChannelHSCutoff where
  q := qP
  q_pos := hqP0'
  q_le_one := hqP1
  cutoff := Ntr
  cutoff_one := by decide
  ratio_lt_one := by
    simpa [channelRatio, rhoP] using hrhoP1

/-- The pilot finite Haar-HS squares converge to a genuine infinite CReal
completion. -/
theorem pilot_heatHaarPartialHSSq_converges :
    CReal.ConvergesTo
      (heatHaarPartialHSSq pilotHeatChannelHSCutoff)
      (heatChannelHSSq pilotHeatChannelHSCutoff) :=
  heatHaarPartialHSSq_converges pilotHeatChannelHSCutoff

end YMGap.Continuum.SU2HeatChannelHilbertSchmidtCompletion

#print axioms YMGap.Continuum.SU2HeatChannelHilbertSchmidtCompletion.channelCoeffSq_geoDom
#print axioms YMGap.Continuum.SU2HeatChannelHilbertSchmidtCompletion.squaredTailWindow_le
#print axioms YMGap.Continuum.SU2HeatChannelHilbertSchmidtCompletion.squaredTailCR
#print axioms YMGap.Continuum.SU2HeatChannelHilbertSchmidtCompletion.heatHSPartial_converges
#print axioms YMGap.Continuum.SU2HeatChannelHilbertSchmidtCompletion.heatHaarPartialHSSq_converges
#print axioms YMGap.Continuum.SU2HeatChannelHilbertSchmidtCompletion.heatHaarRiemann_converges
#print axioms YMGap.Continuum.SU2HeatChannelHilbertSchmidtCompletion.heatChannelHSSq_nonneg
#print axioms YMGap.Continuum.SU2HeatChannelHilbertSchmidtCompletion.pilot_heatHaarPartialHSSq_converges
