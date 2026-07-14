/-
# Located spectrum of the finite SU(2) character-packet transfer

`SU2FiniteCharacterPacketWilsonTransfer` proves a cutoff-independent squared
Gram contraction by `1/64` on packets whose vacuum coefficient vanishes.  This
module turns that estimate into a genuine finite-dimensional located-spectrum
statement without changing the state.

The vacuum-free carrier is first recorded as Type-level data and quotiented by
coefficientwise `Q'` equivalence.  The transfer preserves this subspace and
descends to the quotient.  For a representative `P`, the spectral weight of
the excited label `s = i+1` is

    packetEigen s * coeff(P,s)^2,

which is exactly the interacting Wilson Gram weight, not a free-Haar proxy.
The diagonal eigenvalue is `packetEigen s ^ 2`, because one step of the model
is the squared same-state transfer.  Consequently `corr 0` is the original
interacting Gram and `corr 1` is the Gram after applying the packet transfer
to both arguments.

Every squared excited eigenvalue is at most `(1/8)^2 = 1/64`.  We therefore
construct a `LocatedSpectralGap` for the concrete finite diagonal operator,
with gap margin `63/64`; when the cutoff contains the fundamental mode, its
computed `specMax` is exactly `1/64` up to `Q'.eqv`.

Honest scope: this is spectral localization of the exact one-link character
packet and its same-link iterates.  It does not identify the packet quotient
with the overlapping four-dimensional plaquette GNS space.  That shared-link
and multi-link compatibility is the remaining physical bridge.

The module is constructive and Mathlib-free.  Its dependency gates permit only the
repository-standard `propext` / `Quot.sound`.
-/

import YMGap.Continuum.SU2FiniteCharacterPacketWilsonTransfer
import YMGap.Continuum.CompactTransferGNS

namespace YMGap.Continuum.SU2FiniteCharacterPacketSpectralLocalization

open YMGap.Constructive
open YMGap.Constructive.QPoly
open YMGap.Constructive.RationalTail
open YMGap.Continuum
open YMGap.Continuum.BondMovingStep
open YMGap.Continuum.CompactTransferGNS
open YMGap.Continuum.GNSQuotient
open YMGap.Continuum.SpectralGap
open YMGap.Continuum.SU2CharacterVacuumHaar
open YMGap.Continuum.SU2FiniteCharacterPacketWilsonTransfer

local infix:50 " ≈ " => Q'.eqv

private theorem neg_num_cast (a : Q') : (-a).num = -(a.num) := rfl
private theorem zero_num_cast : (0 : Q').num = 0 := rfl
private theorem zero_den_cast : ((0 : Q').den : Int) = 1 := rfl
private theorem one_num_cast : (1 : Q').num = 1 := rfl
private theorem one_den_cast : ((1 : Q').den : Int) = 1 := rfl

local macro "ring_qeqv" : tactic =>
  `(tactic| (show _ * (_ : Int) = _ * (_ : Int);
             simp only [Q'.add_num_cast, Q'.add_den_cast, Q'.mul_num_cast,
               Q'.mul_den_cast, Q'.neg_den, neg_num_cast, Int.add_mul, Int.mul_add,
               zero_num_cast, zero_den_cast, one_num_cast, one_den_cast,
               Int.neg_mul, Int.mul_neg, Int.neg_add, Int.neg_neg, Int.one_mul,
               Int.mul_one, Int.zero_mul, Int.mul_zero, Int.zero_add, Int.add_zero];
             ac_rfl))

/-! ## The vacuum-free subspace and its coefficient quotient -/

/-- A finite character packet together with the computationally relevant
condition that its vacuum coefficient vanishes.  The packet remains data in
`Type`; no witness is erased in `Prop`-level existence. -/
structure VacuumFreePacket (N : Nat) : Type where
  packet : CharacterPacket N
  vacuum_zero : coeffAt packet 0 ≈ 0

/-- The packet transfer preserves the vacuum-free subspace. -/
def vacuumFreeTransfer {N : Nat} (P : VacuumFreePacket N) : VacuumFreePacket N where
  packet := packetTransfer P.packet
  vacuum_zero := by
    refine Q'.eqv_trans _ _ _ (coeffAt_packetTransfer P.packet 0) ?_
    rw [packetEigen_zero]
    exact Q'.eqv_trans _ _ _ (Q'.one_mul_eqv _) P.vacuum_zero

/-- Coefficientwise equivalence on the vacuum-free subspace. -/
def VacuumFreeEqv {N : Nat} (P Q : VacuumFreePacket N) : Prop :=
  PacketEqv P.packet Q.packet

theorem vacuumFreeEqv_refl {N : Nat} (P : VacuumFreePacket N) :
    VacuumFreeEqv P P := fun _ => Q'.eqv_refl _

theorem vacuumFreeEqv_symm {N : Nat} {P Q : VacuumFreePacket N}
    (h : VacuumFreeEqv P Q) : VacuumFreeEqv Q P :=
  fun i => Q'.eqv_symm (h i)

theorem vacuumFreeEqv_trans {N : Nat} {P Q R : VacuumFreePacket N}
    (hPQ : VacuumFreeEqv P Q) (hQR : VacuumFreeEqv Q R) : VacuumFreeEqv P R :=
  fun i => Q'.eqv_trans _ _ _ (hPQ i) (hQR i)

def vacuumFreeSetoid (N : Nat) : Setoid (VacuumFreePacket N) where
  r := VacuumFreeEqv
  iseqv := ⟨vacuumFreeEqv_refl, vacuumFreeEqv_symm, vacuumFreeEqv_trans⟩

/-- The coefficient-setoid quotient of the vacuum-free packet subspace. -/
def VacuumFreeQuotient (N : Nat) : Type := Quotient (vacuumFreeSetoid N)

theorem vacuumFreeTransfer_congr {N : Nat} {P Q : VacuumFreePacket N}
    (h : VacuumFreeEqv P Q) :
    VacuumFreeEqv (vacuumFreeTransfer P) (vacuumFreeTransfer Q) := by
  intro i
  exact Q'.mul_eqv_congr_left (packetEigen i.val) _ _ (h i)

theorem coeffAt_vacuumFreeEqv {N : Nat} {P Q : VacuumFreePacket N}
    (h : VacuumFreeEqv P Q) (s : Nat) :
    coeffAt P.packet s ≈ coeffAt Q.packet s := by
  by_cases hs : s < N + 1
  · rw [coeffAt_of_lt P.packet hs, coeffAt_of_lt Q.packet hs]
    exact h ⟨s, hs⟩
  · unfold coeffAt
    rw [dif_neg hs, dif_neg hs]
    exact Q'.eqv_refl 0

/-- The exact packet transfer descends to the coefficient quotient. -/
def vacuumFreeTransferQuotient {N : Nat} :
    VacuumFreeQuotient N → VacuumFreeQuotient N :=
  Quotient.lift
    (fun P => Quotient.mk (vacuumFreeSetoid N) (vacuumFreeTransfer P))
    (fun _ _ h => Quotient.sound (vacuumFreeTransfer_congr h))

theorem vacuumFreeTransferQuotient_mk {N : Nat} (P : VacuumFreePacket N) :
    vacuumFreeTransferQuotient
        (Quotient.mk (vacuumFreeSetoid N) P) =
      Quotient.mk (vacuumFreeSetoid N) (vacuumFreeTransfer P) := rfl

/-- The interacting Wilson squared norm respects coefficient equivalence. -/
theorem packetWilsonGram_vacuumFreeEqv {N : Nat} {P Q : VacuumFreePacket N}
    (h : VacuumFreeEqv P Q) :
    packetWilsonGram P.packet P.packet ≈
      packetWilsonGram Q.packet Q.packet := by
  refine Q'.eqv_trans _ _ _ (packetWilsonGram_diagonal P.packet P.packet) ?_
  refine Q'.eqv_trans _ _ _
    (CubeRatioBounds.fsum_eqv_congr _ _ (fun s =>
      Q'.mul_eqv_congr_left (packetEigen s) _ _
        (Q'.eqv_trans _ _ _
          (Q'.mul_eqv_congr_right _ _ _ (coeffAt_vacuumFreeEqv h s))
          (Q'.mul_eqv_congr_left _ _ _ (coeffAt_vacuumFreeEqv h s)))) (N + 1)) ?_
  exact Q'.eqv_symm (packetWilsonGram_diagonal Q.packet Q.packet)

/-- The SAME interacting Wilson squared norm descends to the coefficient
quotient, valued in the rational setoid quotient `QR`. -/
def vacuumFreeNormSq {N : Nat} : VacuumFreeQuotient N → QR :=
  Quotient.lift
    (fun P => Quotient.mk qSetoid (packetWilsonGram P.packet P.packet))
    (fun _ _ h => Quotient.sound (packetWilsonGram_vacuumFreeEqv h))

theorem vacuumFreeNormSq_mk {N : Nat} (P : VacuumFreePacket N) :
    vacuumFreeNormSq (Quotient.mk (vacuumFreeSetoid N) P) =
      Quotient.mk qSetoid (packetWilsonGram P.packet P.packet) := rfl

/-! ## The same interacting Gram as a finite spectral model -/

/-- The squared same-state transfer eigenvalue on the excited label `i+1`. -/
def packetSquaredEigen (i : Nat) : Q' :=
  packetEigen (i + 1) * packetEigen (i + 1)

theorem packetSquaredEigen_nonneg (i : Nat) :
    (0 : Q') ≤ packetSquaredEigen i :=
  Q'.mul_nonneg _ _ (packetEigen_nonneg (i + 1)) (packetEigen_nonneg (i + 1))

/-- The interacting Wilson Gram weight of the excited label `i+1`. -/
def packetExcitedWeight {N : Nat} (P : VacuumFreePacket N) (i : Nat) : Q' :=
  packetEigen (i + 1) *
    (coeffAt P.packet (i + 1) * coeffAt P.packet (i + 1))

theorem packetExcitedWeight_nonneg {N : Nat} (P : VacuumFreePacket N) (i : Nat) :
    (0 : Q') ≤ packetExcitedWeight P i :=
  Q'.mul_nonneg _ _ (packetEigen_nonneg (i + 1))
    (YMGap.Constructive.SumOfSquares.q_mul_self_nonneg
      (coeffAt P.packet (i + 1)))

/-- The finite spectral model of the squared packet transfer.  It is realized
by the concrete diagonal `FiniteOp` of `CompactTransferGNS`; its weights are
the original interacting Wilson Gram weights. -/
def packetSquaredSpectralModel {N : Nat} (P : VacuumFreePacket N) : SpectralModel :=
  diagOp.toSpectralModel packetSquaredEigen (packetExcitedWeight P) N
    (packetExcitedWeight_nonneg P) packetSquaredEigen_nonneg

/-- The finite concrete operator underlying `packetSquaredSpectralModel`. -/
def packetSquaredOp (N : Nat) : FiniteOp := diagOp packetSquaredEigen N

/-- The model eigenvalue is the coordinate eigenvalue of the concrete
finite-dimensional operator. -/
theorem packetSquaredModel_lam_is_eigen {N : Nat} (P : VacuumFreePacket N)
    (i : Nat) (hi : i < N) :
    ((packetSquaredSpectralModel P).lam i) ≈
      ((packetSquaredOp N).apply (basis i) i) :=
  toSpectralModel_lam_is_eigen packetSquaredEigen (packetExcitedWeight P) N
    (packetExcitedWeight_nonneg P) packetSquaredEigen_nonneg i hi

/-- Peel the vacuum term from a finite `fsum`. -/
theorem fsum_shift_cons (f : Nat → Q') : ∀ n,
    fsum f (n + 1) ≈ f 0 + fsum (fun i => f (i + 1)) n
  | 0 =>
      Q'.eqv_trans _ _ _ (QPoly.q_zero_add_eqv (f 0))
        (Q'.eqv_symm (QPoly.q_add_zero_eqv (f 0)))
  | n + 1 => by
      show fsum f (n + 1) + f (n + 1) ≈
        f 0 + (fsum (fun i => f (i + 1)) n + f (n + 1))
      exact Q'.eqv_trans _ _ _
        (Q'.add_eqv_congr_right _ _ _ (fsum_shift_cons f n))
        (Q'.add_assoc_eqv (f 0) (fsum (fun i => f (i + 1)) n) (f (n + 1)))

private theorem vacuum_term_zero {N : Nat} (P : VacuumFreePacket N) :
    packetEigen 0 * (coeffAt P.packet 0 * coeffAt P.packet 0) ≈ 0 := by
  rw [packetEigen_zero]
  refine Q'.eqv_trans _ _ _ (Q'.one_mul_eqv _) ?_
  exact Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_right _ _ _ P.vacuum_zero)
    (Q'.zero_mul_eqv _)

private theorem transferred_vacuum_term_zero {N : Nat} (P : VacuumFreePacket N) :
    packetEigen 0 *
        ((packetEigen 0 * coeffAt P.packet 0) *
          (packetEigen 0 * coeffAt P.packet 0)) ≈ 0 := by
  rw [packetEigen_zero]
  refine Q'.eqv_trans _ _ _ (Q'.one_mul_eqv _) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_right _ _ _
      (Q'.eqv_trans _ _ _ (Q'.one_mul_eqv _) P.vacuum_zero)) ?_
  exact Q'.zero_mul_eqv _

/-- The model's time-zero correlator is exactly the original interacting
Wilson Gram on a vacuum-free packet. -/
theorem packetGram_eq_squaredCorr_zero {N : Nat} (P : VacuumFreePacket N) :
    packetWilsonGram P.packet P.packet ≈
      corr (packetSquaredSpectralModel P) 0 := by
  let term := fun s =>
    packetEigen s * (coeffAt P.packet s * coeffAt P.packet s)
  refine Q'.eqv_trans _ (fsum term (N + 1)) _
    (packetWilsonGram_diagonal P.packet P.packet) ?_
  refine Q'.eqv_trans _ (term 0 + fsum (fun i => term (i + 1)) N) _
    (fsum_shift_cons term N) ?_
  refine Q'.eqv_trans _ (0 + fsum (fun i => term (i + 1)) N) _
    (Q'.add_eqv_congr_right _ _ _ (vacuum_term_zero P)) ?_
  refine Q'.eqv_trans _ (fsum (fun i => term (i + 1)) N) _
    (QPoly.q_zero_add_eqv _) ?_
  rw [YMGap.Continuum.MovingCutoff.fsum_eq_finSum]
  exact Q'.eqv_symm (corr_zero (packetSquaredSpectralModel P))

/-- After applying the packet transfer to both arguments, the same interacting
Gram is exactly the time-one correlator of the squared-transfer model. -/
theorem packetTransferredGram_eq_squaredCorr_one {N : Nat}
    (P : VacuumFreePacket N) :
    packetWilsonGram (packetTransfer P.packet) (packetTransfer P.packet) ≈
      corr (packetSquaredSpectralModel P) 1 := by
  let term := fun s => packetEigen s *
    ((packetEigen s * coeffAt P.packet s) *
      (packetEigen s * coeffAt P.packet s))
  refine Q'.eqv_trans _ (fsum term (N + 1)) _
    (packetWilsonGram_transfer_diagonal P.packet) ?_
  refine Q'.eqv_trans _ (term 0 + fsum (fun i => term (i + 1)) N) _
    (fsum_shift_cons term N) ?_
  refine Q'.eqv_trans _ (0 + fsum (fun i => term (i + 1)) N) _
    (Q'.add_eqv_congr_right _ _ _ (transferred_vacuum_term_zero P)) ?_
  refine Q'.eqv_trans _ (fsum (fun i => term (i + 1)) N) _
    (QPoly.q_zero_add_eqv _) ?_
  rw [YMGap.Continuum.MovingCutoff.fsum_eq_finSum]
  exact SpectralGap.finSum_eqv_of_termwise _ _ (fun i => by
    change term (i + 1) ≈
      packetExcitedWeight P i * (packetSquaredEigen i ^ 1)
    unfold term packetExcitedWeight packetSquaredEigen
    rw [Q'.pow_succ, Q'.pow_zero]
    ring_qeqv) N

/-! ## Exact located separator `1/64` -/

/-- The squared spectral edge inherited from the exact fundamental
eigenvalue `1/8`. -/
def packetSquaredSep : Q' :=
  SU2PeterWeylWilsonBlock.eighth * SU2PeterWeylWilsonBlock.eighth

theorem packetSquaredEigen_le_sep (i : Nat) :
    packetSquaredEigen i ≤ packetSquaredSep := by
  have h0 : (0 : Q') ≤ packetEigen (i + 1) := packetEigen_nonneg (i + 1)
  have he : packetEigen (i + 1) ≤ SU2PeterWeylWilsonBlock.eighth :=
    packetEigen_excited_le_eighth (by omega)
  have h1 := Q'.mul_le_mul_of_nonneg_right _ _ (packetEigen (i + 1)) he h0
  have h2 := Q'.mul_le_mul_of_nonneg_left _ _
    SU2PeterWeylWilsonBlock.eighth he (by decide)
  exact Q'.le_trans' _ _ _ h1 h2

theorem packetSquaredSep_lt_one : packetSquaredSep < (1 : Q') := by decide

/-- A located spectral gap for the concrete squared packet transfer operator,
uniform in both the packet and the cutoff. -/
def packetSquaredLocatedGap {N : Nat} (P : VacuumFreePacket N) :
    LocatedSpectralGap (packetSquaredSpectralModel P) :=
  diagLocatedGap packetSquaredEigen (packetExcitedWeight P) N
    (packetExcitedWeight_nonneg P) packetSquaredEigen_nonneg
    packetSquaredSep packetSquaredSep_lt_one packetSquaredEigen_le_sep

theorem packetSquared_gapMargin_pos {N : Nat} (P : VacuumFreePacket N) :
    (0 : Q') < (packetSquaredLocatedGap P).gapMargin :=
  (packetSquaredLocatedGap P).gapMargin_pos

/-- The located gap margin is exactly `1 - 1/64 = 63/64`. -/
theorem packetSquared_gapMargin_exact {N : Nat} (P : VacuumFreePacket N) :
    (packetSquaredLocatedGap P).gapMargin ≈ Q'.mkPos 63 64 (by decide) := by
  change ((1 : Q') - packetSquaredSep) ≈ Q'.mkPos 63 64 (by decide)
  decide

/-- The spectral decay theorem reproduces the exact `1/64` squared-norm
contraction on the SAME interacting Gram. -/
theorem sameGram_contraction_from_locatedSpectrum {N : Nat}
    (P : VacuumFreePacket N) :
    packetWilsonGram (packetTransfer P.packet) (packetTransfer P.packet) ≤
      packetSquaredSep * packetWilsonGram P.packet P.packet := by
  have hdec := (packetSquaredLocatedGap P).decay 1
  rw [Q'.pow_succ, Q'.pow_zero] at hdec
  refine Q'.le_trans' _ _ _
    (Q'.le_of_eqv (packetTransferredGram_eq_squaredCorr_one P)) ?_
  refine Q'.le_trans' _ _ _ hdec ?_
  refine Q'.le_of_eqv ?_
  refine Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_left (corr (packetSquaredSpectralModel P) 0) _ _
      (Q'.mul_one_eqv packetSquaredSep)) ?_
  refine Q'.eqv_trans _ _ _ (Q'.mul_comm_eqv _ packetSquaredSep) ?_
  exact Q'.mul_eqv_congr_left packetSquaredSep _ _
    (Q'.eqv_symm (packetGram_eq_squaredCorr_zero P))

/-! ## Attainment of the located edge -/

private theorem le_max'_left (a b : Q') : a ≤ Q'.max' a b :=
  ((max'_le_iff a b (Q'.max' a b)).mp (Q'.le_refl' _)).1

private theorem le_max'_right (a b : Q') : b ≤ Q'.max' a b :=
  ((max'_le_iff a b (Q'.max' a b)).mp (Q'.le_refl' _)).2

private theorem le_specMaxAux (lam : Nat → Q') :
    ∀ n j, j < n → lam j ≤ specMaxAux lam n
  | 0, j, hj => absurd hj (Nat.not_lt_zero j)
  | n + 1, j, hj => by
      show lam j ≤ Q'.max' (specMaxAux lam n) (lam n)
      rcases Nat.lt_or_ge j n with hjn | hjn
      · exact Q'.le_trans' _ _ _ (le_specMaxAux lam n j hjn)
          (le_max'_left (specMaxAux lam n) (lam n))
      · have hje : j = n := Nat.le_antisymm (Nat.lt_succ_iff.mp hj) hjn
        subst hje
        exact le_max'_right (specMaxAux lam j) (lam j)

private theorem eqv_of_le_of_ge {a b : Q'} (hab : a ≤ b) (hba : b ≤ a) :
    a ≈ b := by
  exact Int.le_antisymm hab hba

/-- If the packet cutoff contains the fundamental excited mode, the computed
top of the squared spectrum is not merely bounded by `1/64`: it is attained
there, hence is exactly `1/64` up to rational equivalence. -/
theorem packetSquared_specMax_eq_edge {N : Nat} (P : VacuumFreePacket N)
    (hN : 0 < N) :
    specMax (packetSquaredSpectralModel P) ≈ packetSquaredSep := by
  have hedge : packetSquaredEigen 0 ≈ packetSquaredSep := by
    unfold packetSquaredEigen packetSquaredSep
    have h := packetEigen_one
    exact Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_right _ _ _ h)
      (Q'.mul_eqv_congr_left _ _ _ h)
  have hl : packetSquaredSep ≤ specMax (packetSquaredSpectralModel P) :=
    Q'.le_trans' _ _ _ (Q'.ge_of_eqv hedge)
      (le_specMaxAux (packetSquaredSpectralModel P).lam N 0 hN)
  have hr : specMax (packetSquaredSpectralModel P) ≤ packetSquaredSep :=
    (packetSquaredLocatedGap P).located
  exact eqv_of_le_of_ge hr hl

end YMGap.Continuum.SU2FiniteCharacterPacketSpectralLocalization

#print axioms YMGap.Continuum.SU2FiniteCharacterPacketSpectralLocalization.vacuumFreeTransfer
#print axioms YMGap.Continuum.SU2FiniteCharacterPacketSpectralLocalization.vacuumFreeTransferQuotient
#print axioms YMGap.Continuum.SU2FiniteCharacterPacketSpectralLocalization.vacuumFreeNormSq
#print axioms YMGap.Continuum.SU2FiniteCharacterPacketSpectralLocalization.packetSquaredModel_lam_is_eigen
#print axioms YMGap.Continuum.SU2FiniteCharacterPacketSpectralLocalization.packetGram_eq_squaredCorr_zero
#print axioms YMGap.Continuum.SU2FiniteCharacterPacketSpectralLocalization.packetTransferredGram_eq_squaredCorr_one
#print axioms YMGap.Continuum.SU2FiniteCharacterPacketSpectralLocalization.packetSquaredLocatedGap
#print axioms YMGap.Continuum.SU2FiniteCharacterPacketSpectralLocalization.packetSquared_gapMargin_exact
#print axioms YMGap.Continuum.SU2FiniteCharacterPacketSpectralLocalization.sameGram_contraction_from_locatedSpectrum
#print axioms YMGap.Continuum.SU2FiniteCharacterPacketSpectralLocalization.packetSquared_specMax_eq_edge
