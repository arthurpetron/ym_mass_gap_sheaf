/-
Track 11.7-fusion / R2j -- common-denominator certificates for the fence family.

# Result

Direct evaluation of the rational `bondMovedCoeff` expression becomes costly as
the cutoff grows because each summand carries a separately normalized rational.
At the fixed physical fence `w=11/12`, this module instead multiplies the whole
coefficient by the common denominator `12^(2*C4(N))` and evaluates the resulting
finite double sum in `Nat`.

The symbolic reconstruction theorem `scaledCoeff_reconstruct` proves once and
for all that this integer evaluator is exactly the physical coefficient.  The
order bridge `integralTailAt_sound` then turns the cleared comparison

```text
(s+1) A_(s+1) 24^(2s+3) <= 23^(2s+3) (s+2) A_s
```

back into the division-free `P2RetunedCoeffTailRatio` atom.  Kernel reduction
checks all atoms through cutoffs `N=20` and `N=40`, yielding genuine
`CanonicalBulkControl` values while keeping the large computation in `Nat`.
These finite cells are evidence for, not a replacement for, the still-open
all-cutoff coefficient inequality.

# Constructivity

Pure `Nat`, `Int`, and `Q'` induction plus existing Peter--Weyl identities.  No
`Classical`, `native_decide`, `sorry`, custom axiom, or noncomputable declaration.
-/

import YMGap.Continuum.P2RetunedRatioCertificate

namespace YMGap.Continuum.P2RetunedFenceIntegralCertificate

set_option maxRecDepth 30000
set_option exponentiation.threshold 5000
set_option maxHeartbeats 4000000

open YMGap.Continuum
open YMGap.Continuum.RGTransport
open YMGap.Continuum.BondMovingStep
open YMGap.Constructive
open YMGap.Continuum.RebasedBulkLocalizationBridge
open YMGap.Continuum.RebasedBulkShift
open YMGap.Continuum.P2RetunedRatioCompiler

local infix:50 " ≈ " => Q'.eqv

def natSum (f : Nat -> Nat) : Nat -> Nat
  | 0 => 0
  | n + 1 => natSum f n + f n

def scaledTerm (N s a b : Nat) : Nat :=
  if fusionOK a b s then
    (a + 1) * (b + 1) * 11 ^ (c4 a + c4 b) *
      12 ^ (2 * c4 N - (c4 a + c4 b))
  else 0

def scaledCoeff (N s : Nat) : Nat :=
  natSum (fun a => natSum (fun b => scaledTerm N s a b) (N + 1)) (N + 1)

theorem mkPos_mul_mkPos (an cn : Int) (ad cd : Nat)
    (had : 0 < ad) (hcd : 0 < cd) :
    (Q'.mkPos an ad had * Q'.mkPos cn cd hcd) ≈
      Q'.mkPos (an * cn) (ad * cd) (Nat.mul_pos had hcd) := by
  show (an * cn) * ((Q'.mkPos (an * cn) (ad * cd) _).den : Int) =
    (an * cn) * (((Q'.mkPos an ad had * Q'.mkPos cn cd hcd).den) : Int)
  rw [Q'.mkPos_den, Q'.mul_den_cast, Q'.mkPos_den, Q'.mkPos_den]
  rfl

theorem qpow_fenceW_eqv : forall n : Nat,
    qpow fenceW n ≈
      Q'.mkPos ((11 ^ n : Nat) : Int) (12 ^ n) (Nat.pow_pos (by decide))
  | 0 => by decide
  | n + 1 => by
      unfold qpow
      refine Q'.eqv_trans _ _ _
        (Q'.mul_eqv_congr_right _ _ fenceW (qpow_fenceW_eqv n)) ?_
      simpa only [fenceW, Nat.pow_succ, Int.natCast_mul] using
        mkPos_mul_mkPos ((11 ^ n : Nat) : Int) 11 (12 ^ n) 12
          (Nat.pow_pos (by decide)) (by decide)

theorem scale_monomial_eqv (E e C : Nat) (he : e <= E) :
    Q'.ofNat (12 ^ E) * (Q'.ofNat C * qpow fenceW e) ≈
      Q'.ofNat (C * 11 ^ e * 12 ^ (E - e)) := by
  refine Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_left _ _ _
      (Q'.mul_eqv_congr_left _ _ _ (qpow_fenceW_eqv e))) ?_
  have hE : E = e + (E - e) := by omega
  have hpow : 12 ^ E = 12 ^ e * 12 ^ (E - e) := by
    calc
      12 ^ E = 12 ^ (e + (E - e)) := congrArg (fun n => 12 ^ n) hE
      _ = 12 ^ e * 12 ^ (E - e) := Nat.pow_add 12 e (E - e)
  unfold Q'.eqv
  simp only [Q'.mul_num_cast, Q'.mul_den_cast, Q'.ofNat_num_cast,
    Q'.ofNat_den_cast, Q'.mkPos_num, Q'.mkPos_den]
  rw [hpow]
  push_cast
  simp only [Int.mul_one, Int.one_mul]
  ac_rfl

theorem scaledTerm_eqv (N s a b : Nat) (ha : a < N + 1) (hb : b < N + 1) :
    Q'.ofNat (12 ^ (2 * c4 N)) *
        (fusionInd a b s * (coeffW fenceW a * coeffW fenceW b)) ≈
      Q'.ofNat (scaledTerm N s a b) := by
  have hac : c4 a <= c4 N :=
    YMGap.Continuum.SpectralLocalizationCrux.c4_le_c4 (by omega)
  have hbc : c4 b <= c4 N :=
    YMGap.Continuum.SpectralLocalizationCrux.c4_le_c4 (by omega)
  have he : c4 a + c4 b <= 2 * c4 N := by omega
  unfold fusionInd scaledTerm
  by_cases h : fusionOK a b s
  · simp only [if_pos h]
    refine Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_left _ _ _ ?_) (scale_monomial_eqv _ _ _ he)
    refine Q'.eqv_trans _ _ _ (Q'.one_mul_eqv _) ?_
    exact YMGap.Continuum.FusionRDFactor.coeffW_mul_rd_sym a b
  · simp only [if_neg h]
    refine Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_left _ _ _ (Q'.zero_mul_eqv _)) ?_
    exact YMGap.Constructive.QPoly.q_mul_zero _

theorem scale_fsum_eqv (scale : Q') (fQ : Nat -> Q') (fN : Nat -> Nat) :
    forall n : Nat, (forall i, i < n -> scale * fQ i ≈ Q'.ofNat (fN i)) ->
      scale * fsum fQ n ≈ Q'.ofNat (natSum fN n)
  | 0, _ => YMGap.Constructive.QPoly.q_mul_zero _
  | n + 1, h => by
      refine Q'.eqv_trans _ _ _ (Q'.mul_add_eqv _ _ _) ?_
      refine Q'.eqv_trans _ _ _
        (Q'.add_eqv_congr_right _ _ _
          (scale_fsum_eqv scale fQ fN n (fun i hi => h i (by omega)))) ?_
      refine Q'.eqv_trans _ _ _
        (Q'.add_eqv_congr_left _ _ _ (h n (by omega))) ?_
      exact Q'.eqv_symm (Q'.ofNat_add_eqv (natSum fN n) (fN n))

theorem scaledCoeff_reconstruct (N s : Nat) :
    Q'.ofNat (12 ^ (2 * c4 N)) * bondMovedCoeff N fenceW 2 s ≈
      Q'.ofNat (scaledCoeff N s) := by
  refine Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_left _ _ _
      (YMGap.Continuum.FusionRDFactor.bondMovedCoeff_p2_doubleSum N s)) ?_
  apply scale_fsum_eqv
  intro a ha
  apply scale_fsum_eqv
  intro b hb
  exact scaledTerm_eqv N s a b ha hb

theorem qpow_retuned_eqv : forall k : Nat,
    qpow (p2RetunedWeight fenceW) k ≈
      Q'.mkPos ((23 ^ k : Nat) : Int) (24 ^ k) (Nat.pow_pos (by decide))
  | 0 => by decide
  | k + 1 => by
      unfold qpow
      refine Q'.eqv_trans _ _ _
        (Q'.mul_eqv_congr_right _ _ _ (qpow_retuned_eqv k)) ?_
      refine Q'.eqv_trans _ _ _
        (Q'.mul_eqv_congr_left _ _ _
          YMGap.Continuum.P2RetunedRatioCertificate.fenceRetunedWeight_eqv_23_24) ?_
      simpa only [Nat.pow_succ, Int.natCast_mul] using
        mkPos_mul_mkPos ((23 ^ k : Nat) : Int) 23 (24 ^ k) 24
          (Nat.pow_pos (by decide)) (by decide)

theorem ofNat_le_mkPos_mul_of_cross (A B num den : Nat) (hden : 0 < den)
    (h : A * den <= num * B) :
    Q'.ofNat A <= Q'.mkPos num den hden * Q'.ofNat B := by
  show ((A : Nat) : Int) *
      ((Q'.mkPos num den hden * Q'.ofNat B).den : Int) <=
    ((Q'.mkPos num den hden * Q'.ofNat B).num) * (1 : Int)
  rw [Q'.mul_den_cast, Q'.mkPos_den]
  show ((A : Nat) : Int) * (((den : Nat) : Int) * (1 : Int)) <=
    (((num : Nat) : Int) * ((B : Nat) : Int)) * (1 : Int)
  simp only [Int.mul_one]
  rw [← Int.natCast_mul, ← Int.natCast_mul]
  exact Int.ofNat_le.mpr h

theorem scale_dim_coeff_reconstruct (N mode coeffMode : Nat) :
    Q'.ofNat (12 ^ (2 * c4 N)) *
        (dimQ mode * bondMovedCoeff N fenceW 2 coeffMode) ≈
      Q'.ofNat ((mode + 1) * scaledCoeff N coeffMode) := by
  refine Q'.eqv_trans _ _ _ (Q'.eqv_symm (Q'.mul_assoc_eqv _ _ _)) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_right _ _ _ (Q'.mul_comm_eqv _ _)) ?_
  refine Q'.eqv_trans _ _ _ (Q'.mul_assoc_eqv _ _ _) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_left _ _ _ (scaledCoeff_reconstruct N coeffMode)) ?_
  exact Q'.eqv_symm
    (YMGap.Continuum.FusionRDFactor.ofNat_mul_eqv (mode + 1)
      (scaledCoeff N coeffMode))

theorem scale_retuned_dim_coeff_reconstruct (N s : Nat) :
    Q'.ofNat (12 ^ (2 * c4 N)) *
        (qpow (p2RetunedWeight fenceW) (2 * s + 3) *
          (dimQ (s + 1) * bondMovedCoeff N fenceW 2 s)) ≈
      qpow (p2RetunedWeight fenceW) (2 * s + 3) *
        Q'.ofNat ((s + 2) * scaledCoeff N s) := by
  refine Q'.eqv_trans _ _ _ (Q'.eqv_symm (Q'.mul_assoc_eqv _ _ _)) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_right _ _ _ (Q'.mul_comm_eqv _ _)) ?_
  refine Q'.eqv_trans _ _ _ (Q'.mul_assoc_eqv _ _ _) ?_
  exact Q'.mul_eqv_congr_left _ _ _ (scale_dim_coeff_reconstruct N (s + 1) s)

def integralTailAt (N s : Nat) : Prop :=
  (s + 1) * scaledCoeff N (s + 1) * 24 ^ (2 * s + 3) <=
    23 ^ (2 * s + 3) * ((s + 2) * scaledCoeff N s)

instance integralTailAtDecidable (N s : Nat) : Decidable (integralTailAt N s) := by
  unfold integralTailAt
  infer_instance

def integralTailBlockCheck (N start length : Nat) : Bool :=
  (List.range length).all fun i => decide (integralTailAt N (start + i))

theorem integralTailAt_sound {N s : Nat} (h : integralTailAt N s) :
    dimQ s * bondMovedCoeff N fenceW 2 (s + 1) <=
      qpow (p2RetunedWeight fenceW) (2 * s + 3) *
        (dimQ (s + 1) * bondMovedCoeff N fenceW 2 s) := by
  let scale := Q'.ofNat (12 ^ (2 * c4 N))
  let k := 2 * s + 3
  have hcross :
      (s + 1) * scaledCoeff N (s + 1) * 24 ^ k <=
        23 ^ k * ((s + 2) * scaledCoeff N s) := by
    simpa only [k] using h
  have hrat := ofNat_le_mkPos_mul_of_cross
    ((s + 1) * scaledCoeff N (s + 1))
    ((s + 2) * scaledCoeff N s) (23 ^ k) (24 ^ k)
      (Nat.pow_pos (by decide)) hcross
  have hcore :
      Q'.ofNat ((s + 1) * scaledCoeff N (s + 1)) <=
        qpow (p2RetunedWeight fenceW) k *
          Q'.ofNat ((s + 2) * scaledCoeff N s) :=
    Q'.le_trans' _ _ _ hrat (Q'.le_of_eqv
      (Q'.mul_eqv_congr_right _ _ _ (Q'.eqv_symm (qpow_retuned_eqv k))))
  have hl := scale_dim_coeff_reconstruct N s (s + 1)
  have hr := scale_retuned_dim_coeff_reconstruct N s
  have hscaled :
      scale * (dimQ s * bondMovedCoeff N fenceW 2 (s + 1)) <=
        scale * (qpow (p2RetunedWeight fenceW) k *
          (dimQ (s + 1) * bondMovedCoeff N fenceW 2 s)) :=
    Q'.le_trans' _ _ _ (Q'.le_of_eqv hl)
      (Q'.le_trans' _ _ _ hcore (Q'.le_of_eqv (Q'.eqv_symm hr)))
  have hscale : (0 : Q') < scale := by
    show (0 : Int) * (1 : Int) <
      ((12 ^ (2 * c4 N) : Nat) : Int) * (1 : Int)
    simp only [Int.mul_one]
    exact_mod_cast (Nat.pow_pos (by decide : 0 < 12))
  exact Q'.le_of_mul_le_mul_left hscaled hscale

theorem integralTailBlockCheck_sound {N start length s : Nat}
    (hcheck : integralTailBlockCheck N start length = true)
    (hlo : start <= s) (hhi : s < start + length) :
    dimQ s * bondMovedCoeff N fenceW 2 (s + 1) <=
      qpow (p2RetunedWeight fenceW) (2 * s + 3) *
        (dimQ (s + 1) * bondMovedCoeff N fenceW 2 s) := by
  have hi : s - start < length := by omega
  have hmem : s - start ∈ List.range length := List.mem_range.mpr hi
  have hrow := List.all_eq_true.mp hcheck (s - start) hmem
  have hsEq : start + (s - start) = s := by omega
  apply integralTailAt_sound
  simpa only [hsEq] using of_decide_eq_true hrow

def coeffTailRatio_of_integralCheck (N : Nat)
    (hcheck : integralTailBlockCheck N 1 (2 * N - 1) = true) :
    P2RetunedCoeffTailRatio N fenceW fenceW_nonneg fenceW_le_one where
  tail := fun s hs1 hsN =>
    integralTailBlockCheck_sound hcheck hs1 (by omega)

theorem checkN20 : integralTailBlockCheck 20 1 39 = true := by decide

theorem checkN40 : integralTailBlockCheck 40 1 79 = true := by decide

def fenceRetunedControlN20 :
    CanonicalBulkControl 20 fenceW 2 :=
  canonicalBulkControl_p2_of_coeffTail (by decide) fenceW_nonneg fenceW_le_one
    fenceW_near_continuum (coeffTailRatio_of_integralCheck 20 (by simpa using checkN20))

def fenceRetunedControlN40 :
    CanonicalBulkControl 40 fenceW 2 :=
  canonicalBulkControl_p2_of_coeffTail (by decide) fenceW_nonneg fenceW_le_one
    fenceW_near_continuum (coeffTailRatio_of_integralCheck 40 (by simpa using checkN40))

end YMGap.Continuum.P2RetunedFenceIntegralCertificate

/-! ## Axiom-dependency gates -/

#print axioms YMGap.Continuum.P2RetunedFenceIntegralCertificate.qpow_fenceW_eqv
#print axioms YMGap.Continuum.P2RetunedFenceIntegralCertificate.scaledCoeff_reconstruct
#print axioms YMGap.Continuum.P2RetunedFenceIntegralCertificate.integralTailAt_sound
#print axioms YMGap.Continuum.P2RetunedFenceIntegralCertificate.checkN20
#print axioms YMGap.Continuum.P2RetunedFenceIntegralCertificate.checkN40
#print axioms YMGap.Continuum.P2RetunedFenceIntegralCertificate.fenceRetunedControlN20
#print axioms YMGap.Continuum.P2RetunedFenceIntegralCertificate.fenceRetunedControlN40
