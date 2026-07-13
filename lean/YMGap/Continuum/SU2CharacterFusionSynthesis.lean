/-
# Exact synthesis of the SU(2) fusion packet

This module proves the finite combinatorial bridge left open by
`SU2ClassPolynomialPacketDescent`: the indicator-defined fusion packet really
synthesizes to pointwise multiplication of its two input character sums.

The first checkpoint is the single-row identity.  Scanning the output mode
from zero through `2*N`, the `fusionInd a b` row has support exactly on the
ascending Clebsch--Gordan ladder

    |a-b|, |a-b|+2, ..., a+b.

A constructive prefix induction reindexes that sparse row to the existing
`Ufusion` sum.  No permutation choice or finite-set quotient is used.

# Axiom gate

All declarations are MLTT/HoTT-clean up to `propext` / `Quot.sound`.  There is
no classical choice, trusted native computation, proof hole, or custom axiom.
-/

import YMGap.Continuum.SU2ClassPolynomialPacketDescent
import YMGap.Continuum.FusionBratteli

namespace YMGap.Continuum.SU2CharacterFusionSynthesis

open YMGap.Constructive
open YMGap.Constructive.QPoly
open YMGap.Constructive.RationalTail
open YMGap.Continuum.BondMovingStep
open YMGap.Continuum.FusionQuotientCollapse
open YMGap.Continuum.SU2ClassPolynomialAlgebra
open YMGap.Continuum.SU2CharacterVacuumHaar

private theorem fusionLow_top (a b : Nat) :
    ChebOrthogonality.fusionLow a b + 2 * min a b = a + b := by
  by_cases h : a <= b
  · simp [ChebOrthogonality.fusionLow, Nat.min_eq_left h,
      Nat.max_eq_right h]
    omega
  · have hba : b <= a := by omega
    simp [ChebOrthogonality.fusionLow, Nat.min_eq_right hba,
      Nat.max_eq_left hba]
    omega

/-- Ascending-ladder form of the fusion predicate. -/
theorem fusionOK_iff_ascending (a b s : Nat) :
    fusionOK a b s = true <->
      Exists fun r => r <= min a b /\
        s = ChebOrthogonality.fusionLow a b + 2 * r := by
  rw [YMGap.Continuum.FusionBratteli.fusionOK_iff_ladder]
  constructor
  · rintro ⟨k, hka, hkb, heq⟩
    refine ⟨min a b - k, by omega, ?_⟩
    have htop := fusionLow_top a b
    omega
  · rintro ⟨r, hr, hs⟩
    refine ⟨min a b - r, by omega, by omega, ?_⟩
    have htop := fusionLow_top a b
    omega

private theorem fusionInd_one_of_ascending (a b r : Nat)
    (hr : r <= min a b) :
    fusionInd a b (ChebOrthogonality.fusionLow a b + 2 * r) = 1 := by
  unfold fusionInd
  rw [if_pos ((fusionOK_iff_ascending a b _).2 ⟨r, hr, rfl⟩)]

private theorem fusionInd_zero_below (a b s : Nat)
    (hs : s < ChebOrthogonality.fusionLow a b) :
    fusionInd a b s = 0 := by
  unfold fusionInd
  rw [if_neg]
  intro hok
  obtain ⟨r, _, heq⟩ := (fusionOK_iff_ascending a b s).1 hok
  omega

private theorem fusionInd_zero_odd (a b r : Nat) :
    fusionInd a b (ChebOrthogonality.fusionLow a b + 2 * r + 1) = 0 := by
  unfold fusionInd
  rw [if_neg]
  intro hok
  obtain ⟨j, _, heq⟩ := (fusionOK_iff_ascending a b _).1 hok
  omega

private theorem fusionInd_zero_above (a b s : Nat) (hs : a + b < s) :
    fusionInd a b s = 0 := by
  unfold fusionInd
  rw [if_neg]
  intro hok
  obtain ⟨r, hr, heq⟩ := (fusionOK_iff_ascending a b s).1 hok
  have htop := fusionLow_top a b
  omega

private theorem finSum_congr_lt (f g : Nat -> Q') (n : Nat)
    (h : forall i, i < n -> (f i).eqv (g i)) :
    (finSum f n).eqv (finSum g n) := by
  induction n with
  | zero => exact Q'.eqv_refl _
  | succ m ih =>
      exact q_add_congr
        (ih (fun i hi => h i (Nat.lt_succ_of_lt hi)))
        (h m (Nat.lt_succ_self m))

private theorem finSum_add_range (f : Nat -> Q') (a : Nat) : forall b : Nat,
    (finSum f (a + b)).eqv
      (finSum f a + finSum (fun i => f (a + i)) b)
  | 0 => Q'.eqv_symm (q_add_zero_eqv _)
  | b + 1 => by
      refine Q'.eqv_trans _ _ _
        (q_add_congr (finSum_add_range f a b) (Q'.eqv_refl _)) ?_
      exact Q'.add_assoc_eqv (finSum f a)
        (finSum (fun i => f (a + i)) b) (f (a + b))

private theorem finSum_zero_extension {f : Nat -> Q'} {n m : Nat}
    (hnm : n <= m) (hz : forall i : Nat, n <= i -> (f i).eqv 0) :
    (finSum f m).eqv (finSum f n) := by
  induction hnm with
  | refl => exact Q'.eqv_refl _
  | @step m hnm ih =>
      exact Q'.eqv_trans _ (finSum f n + 0) _
        (q_add_congr ih (hz m hnm)) (q_add_zero_eqv (finSum f n))

private def fusionRowTerm (a b : Nat) (x : Q') (s : Nat) : Q' :=
  fusionInd a b s * Cheb.U s x

private theorem fusionRowTerm_below_zero (a b : Nat) (x : Q') (s : Nat)
    (hs : s < ChebOrthogonality.fusionLow a b) :
    (fusionRowTerm a b x s).eqv 0 := by
  rw [fusionRowTerm, fusionInd_zero_below a b s hs]
  exact q_zero_mul _

private theorem fusionRowTerm_odd_zero (a b r : Nat) (x : Q') :
    (fusionRowTerm a b x
      (ChebOrthogonality.fusionLow a b + 2 * r + 1)).eqv 0 := by
  rw [fusionRowTerm, fusionInd_zero_odd a b r]
  exact q_zero_mul _

private theorem fusionRowTerm_ladder (a b r : Nat) (x : Q')
    (hr : r <= min a b) :
    (fusionRowTerm a b x
      (ChebOrthogonality.fusionLow a b + 2 * r)).eqv
      (Cheb.U (ChebOrthogonality.fusionLow a b + 2 * r) x) := by
  rw [fusionRowTerm, fusionInd_one_of_ascending a b r hr]
  exact Q'.one_mul_eqv _

private theorem fusionRowPrefix (a b : Nat) (x : Q') : forall r : Nat,
    r <= min a b ->
    (finSum (fusionRowTerm a b x)
      (ChebOrthogonality.fusionLow a b + 2 * r + 1)).eqv
      (finSum
        (fun j => Cheb.U (ChebOrthogonality.fusionLow a b + 2 * j) x)
        (r + 1))
  | 0, _ => by
      let low := ChebOrthogonality.fusionLow a b
      have hsplit := finSum_add_range (fusionRowTerm a b x) low 1
      have hbelow :
          (finSum (fusionRowTerm a b x) low).eqv 0 := by
        refine Q'.eqv_trans _ (finSum (fun _ => (0 : Q')) low) _ ?_ ?_
        · exact finSum_congr_lt _ _ low
            (fun i hi => fusionRowTerm_below_zero a b x i hi)
        · exact Q'.eqv_of_eq (RationalTail.finSum_zero_seq low)
      have hcell := fusionRowTerm_ladder a b 0 x (Nat.zero_le _)
      refine Q'.eqv_trans _
        (finSum (fusionRowTerm a b x) low +
          finSum (fun i => fusionRowTerm a b x (low + i)) 1) _
        (by simpa [low] using hsplit) ?_
      show (finSum (fusionRowTerm a b x) low +
          ((0 : Q') + fusionRowTerm a b x low)).eqv
        ((0 : Q') + Cheb.U low x)
      exact Q'.eqv_trans _ (0 + (0 + Cheb.U low x)) _
        (q_add_congr hbelow (q_add_congr (Q'.eqv_refl 0)
          (by simpa [low] using hcell)))
        (Q'.eqv_trans _ _ _ (q_zero_add_eqv _)
          (Q'.eqv_refl _))
  | r + 1, hr => by
      let low := ChebOrthogonality.fusionLow a b
      let old := low + 2 * r + 1
      have hir : r <= min a b := by omega
      have ih := fusionRowPrefix a b x r hir
      have hsplit := finSum_add_range (fusionRowTerm a b x) old 2
      have hodd := fusionRowTerm_odd_zero a b r x
      have hnext := fusionRowTerm_ladder a b (r + 1) x hr
      refine Q'.eqv_trans _
        (finSum (fusionRowTerm a b x) old +
          finSum (fun i => fusionRowTerm a b x (old + i)) 2) _
        (by
          have hcount : low + 2 * (r + 1) + 1 = old + 2 := by
            simp [old, low]
            omega
          rw [hcount]
          exact hsplit) ?_
      show (finSum (fusionRowTerm a b x) old +
          (((0 : Q') + fusionRowTerm a b x old) +
            fusionRowTerm a b x (old + 1))).eqv
        (finSum
          (fun j => Cheb.U (low + 2 * j) x) (r + 1) +
          Cheb.U (low + 2 * (r + 1)) x)
      refine q_add_congr (by simpa [old, low] using ih) ?_
      exact Q'.eqv_trans _ (0 + Cheb.U (low + 2 * (r + 1)) x) _
        (q_add_congr
          (Q'.eqv_trans _ _ _ (q_zero_add_eqv _)
            (by simpa [old, low] using hodd))
          (by simpa [old, low] using hnext))
        (q_zero_add_eqv _)

/-- The finite output-mode indicator row is exactly the existing
Clebsch--Gordan `Ufusion` polynomial value. -/
theorem fusionIndicatorSum_eq_Ufusion {N a b : Nat}
    (ha : a <= N) (hb : b <= N) (x : Q') :
    (finSum (fun s => fusionInd a b s * Cheb.U s x) (2 * N + 1)).eqv
      (ChebOrthogonality.Ufusion a b x) := by
  let top := ChebOrthogonality.fusionLow a b + 2 * min a b + 1
  have htop : top = a + b + 1 := by
    simp [top, fusionLow_top a b]
  have hbound : top <= 2 * N + 1 := by
    rw [htop]
    omega
  refine Q'.eqv_trans _
    (finSum (fusionRowTerm a b x) top) _ ?_ ?_
  · exact finSum_zero_extension hbound (fun s hs => by
      rw [fusionInd_zero_above a b s (by rw [htop] at hs; omega)]
      exact q_zero_mul _)
  · have hp := fusionRowPrefix a b x (min a b) (Nat.le_refl _)
    simpa [fusionRowTerm, top, ChebOrthogonality.Ufusion] using hp

/-! ## Bilinear synthesis and the full packet product -/

private theorem mul_interchange (a b c d : Q') :
    ((a * b) * (c * d)).eqv ((a * c) * (b * d)) := by
  refine Q'.eqv_trans _ (a * (b * (c * d))) _
    (Q'.mul_assoc_eqv a b (c * d)) ?_
  refine Q'.eqv_trans _ (a * ((b * c) * d)) _
    (Q'.mul_eqv_congr_left a _ _
      (Q'.eqv_symm (Q'.mul_assoc_eqv b c d))) ?_
  refine Q'.eqv_trans _ (a * ((c * b) * d)) _
    (Q'.mul_eqv_congr_left a _ _
      (Q'.mul_eqv_congr_right _ _ d (Q'.mul_comm_eqv b c))) ?_
  refine Q'.eqv_trans _ (a * (c * (b * d))) _
    (Q'.mul_eqv_congr_left a _ _ (Q'.mul_assoc_eqv c b d)) ?_
  exact Q'.eqv_symm (Q'.mul_assoc_eqv a c (b * d))

private theorem finSum_product (f g : Nat -> Q') (m n : Nat) :
    (finSum f m * finSum g n).eqv
      (finSum (fun a => finSum (fun b => f a * g b) n) m) := by
  refine Q'.eqv_trans _
    (finSum (fun a => f a * finSum g n) m) _
    (RationalTail.finSum_mul_const f (finSum g n) m) ?_
  exact RationalTail.finSum_eqv_congr _ _ (fun a =>
    RationalTail.const_mul_finSum g (f a) n) m

private theorem fusionCoeff_mul_U_expand {N : Nat}
    (P Q : CharacterPacket N) (s : Nat) (x : Q') :
    (fusionCoeff P Q s * Cheb.U s x).eqv
      (finSum (fun a => finSum (fun b =>
        (fusionInd a b s * (coeffAt P a * coeffAt Q b)) * Cheb.U s x)
        (N + 1)) (N + 1)) := by
  unfold fusionCoeff fusionProduct
  rw [YMGap.Continuum.MovingCutoff.fsum_eq_finSum]
  refine Q'.eqv_trans _
    (finSum (fun a =>
      fsum (fun b => fusionInd a b s * (coeffAt P a * coeffAt Q b))
        (N + 1) * Cheb.U s x) (N + 1)) _
    (RationalTail.finSum_mul_const _ (Cheb.U s x) (N + 1)) ?_
  exact RationalTail.finSum_eqv_congr _ _ (fun a => by
    rw [YMGap.Continuum.MovingCutoff.fsum_eq_finSum]
    exact RationalTail.finSum_mul_const _ (Cheb.U s x) (N + 1)) (N + 1)

private theorem weightedFusionRow {N a b : Nat}
    (ha : a < N + 1) (hb : b < N + 1)
    (P Q : CharacterPacket N) (x : Q') :
    (finSum (fun s =>
      (fusionInd a b s * (coeffAt P a * coeffAt Q b)) * Cheb.U s x)
      (2 * N + 1)).eqv
      ((coeffAt P a * Cheb.U a x) * (coeffAt Q b * Cheb.U b x)) := by
  let c := coeffAt P a * coeffAt Q b
  have hterm : forall s,
      ((fusionInd a b s * (coeffAt P a * coeffAt Q b)) * Cheb.U s x).eqv
        (c * (fusionInd a b s * Cheb.U s x)) := by
    intro s
    unfold c
    refine Q'.eqv_trans _
      ((coeffAt P a * coeffAt Q b) * fusionInd a b s * Cheb.U s x) _
      (Q'.mul_eqv_congr_right _ _ _
        (Q'.mul_comm_eqv (fusionInd a b s)
          (coeffAt P a * coeffAt Q b))) ?_
    exact Q'.mul_assoc_eqv _ _ _
  refine Q'.eqv_trans _
    (finSum (fun s => c * (fusionInd a b s * Cheb.U s x))
      (2 * N + 1)) _
    (RationalTail.finSum_eqv_congr _ _ hterm (2 * N + 1)) ?_
  refine Q'.eqv_trans _
    (c * finSum (fun s => fusionInd a b s * Cheb.U s x) (2 * N + 1)) _
    (Q'.eqv_symm (RationalTail.const_mul_finSum _ c (2 * N + 1))) ?_
  refine Q'.eqv_trans _
    (c * ChebOrthogonality.Ufusion a b x) _
    (Q'.mul_eqv_congr_left c _ _
      (fusionIndicatorSum_eq_Ufusion (by omega) (by omega) x)) ?_
  refine Q'.eqv_trans _
    (c * (Cheb.U a x * Cheb.U b x)) _
    (Q'.mul_eqv_congr_left c _ _
      (Q'.eqv_symm (ChebOrthoMatrix.chebU_fusion a b x))) ?_
  exact mul_interchange (coeffAt P a) (coeffAt Q b)
    (Cheb.U a x) (Cheb.U b x)

/-- **Exact packet multiplication.**  Synthesizing the existing
indicator-defined `fusionPacket` is extensionally equal to ordinary
pointwise multiplication of the two synthesized class polynomials. -/
theorem synthesis_fusionPacket_product {N : Nat} (P Q : CharacterPacket N) :
    PolyEqv (synthesis (fusionPacket P Q))
      (pmul (synthesis P) (synthesis Q)) := by
  intro x
  refine Q'.eqv_trans _
    (finSum (fun s => coeffAt (fusionPacket P Q) s * Cheb.U s x)
      (2 * N + 1)) _
    (eval_synthesis (fusionPacket P Q) x) ?_
  have hcoeff : forall s,
      (coeffAt (fusionPacket P Q) s * Cheb.U s x).eqv
        (fusionCoeff P Q s * Cheb.U s x) := by
    intro s
    by_cases hs : s < 2 * N + 1
    · rw [coeffAt_of_lt (fusionPacket P Q) hs]
      exact Q'.eqv_refl _
    · rw [coeffAt_of_gt (fusionPacket P Q) (by omega)]
      have habove : forall a b, a < N + 1 -> b < N + 1 ->
          fusionInd a b s = 0 := by
        intro a b ha hb
        exact fusionInd_zero_above a b s (by omega)
      have hfc : (fusionCoeff P Q s).eqv 0 := by
        unfold fusionCoeff fusionProduct
        apply fsum_zero_below
        intro a ha
        apply fsum_zero_below
        intro b hb
        rw [habove a b ha hb]
        exact q_zero_mul _
      have hprod : (fusionCoeff P Q s * Cheb.U s x).eqv 0 :=
        Q'.eqv_trans _ _ _
          (Q'.mul_eqv_congr_right _ _ _ hfc) (q_zero_mul _)
      exact Q'.eqv_trans _ 0 _ (q_zero_mul _) (Q'.eqv_symm hprod)
  refine Q'.eqv_trans _
    (finSum (fun s => fusionCoeff P Q s * Cheb.U s x) (2 * N + 1)) _
    (RationalTail.finSum_eqv_congr _ _ hcoeff (2 * N + 1)) ?_
  refine Q'.eqv_trans _
    (finSum (fun s => finSum (fun a => finSum (fun b =>
      (fusionInd a b s * (coeffAt P a * coeffAt Q b)) * Cheb.U s x)
      (N + 1)) (N + 1)) (2 * N + 1)) _
    (RationalTail.finSum_eqv_congr _ _
      (fun s => fusionCoeff_mul_U_expand P Q s x) (2 * N + 1)) ?_
  refine Q'.eqv_trans _
    (finSum (fun a => finSum (fun s => finSum (fun b =>
      (fusionInd a b s * (coeffAt P a * coeffAt Q b)) * Cheb.U s x)
      (N + 1)) (2 * N + 1)) (N + 1)) _
    (RationalTail.finSum_swap
      (fun s a => finSum (fun b =>
        (fusionInd a b s * (coeffAt P a * coeffAt Q b)) * Cheb.U s x)
        (N + 1)) (2 * N + 1) (N + 1)) ?_
  refine Q'.eqv_trans _
    (finSum (fun a => finSum (fun b => finSum (fun s =>
      (fusionInd a b s * (coeffAt P a * coeffAt Q b)) * Cheb.U s x)
      (2 * N + 1)) (N + 1)) (N + 1)) _ ?_ ?_
  · exact RationalTail.finSum_eqv_congr _ _ (fun a =>
      RationalTail.finSum_swap
        (fun s b =>
          (fusionInd a b s * (coeffAt P a * coeffAt Q b)) * Cheb.U s x)
        (2 * N + 1) (N + 1)) (N + 1)
  · refine Q'.eqv_trans _
      (finSum (fun a => finSum (fun b =>
        (coeffAt P a * Cheb.U a x) * (coeffAt Q b * Cheb.U b x))
        (N + 1)) (N + 1)) _ ?_ ?_
    · exact finSum_congr_lt _ _ (N + 1) (fun a ha =>
        finSum_congr_lt _ _ (N + 1) (fun b hb =>
          weightedFusionRow ha hb P Q x))
    · refine Q'.eqv_trans _
        (finSum (fun a => coeffAt P a * Cheb.U a x) (N + 1) *
          finSum (fun b => coeffAt Q b * Cheb.U b x) (N + 1)) _
        (Q'.eqv_symm (finSum_product _ _ (N + 1) (N + 1))) ?_
      refine Q'.eqv_trans _
        (eval (synthesis P) x * eval (synthesis Q) x) _ ?_ ?_
      · exact Q'.eqv_trans _ _ _
          (Q'.mul_eqv_congr_right _ _ _
            (Q'.eqv_symm (eval_synthesis P x)))
          (Q'.mul_eqv_congr_left _ _ _
            (Q'.eqv_symm (eval_synthesis Q x)))
      · exact Q'.eqv_symm (eval_pmul (synthesis P) (synthesis Q) x)

/-- The arbitrary bare-polynomial fusion carrier from packet descent is the
ordinary `QPoly` product, not merely a positive surrogate. -/
theorem polynomialFusionProduct_eq_pmul (p q : Poly) :
    PolyEqv
      (YMGap.Continuum.SU2ClassPolynomialPacketDescent.polynomialFusionProduct p q)
      (pmul p q) := by
  open YMGap.Continuum.SU2ClassPolynomialPacketDescent in
    exact peqv_trans
      (synthesis_fusionPacket_product
        (leftPolynomialPacket p q) (rightPolynomialPacket p q))
      (pmul_congr (synthesis_leftPolynomialPacket p q)
        (synthesis_rightPolynomialPacket p q))

end YMGap.Continuum.SU2CharacterFusionSynthesis

#print axioms YMGap.Continuum.SU2CharacterFusionSynthesis.fusionOK_iff_ascending
#print axioms YMGap.Continuum.SU2CharacterFusionSynthesis.fusionIndicatorSum_eq_Ufusion
#print axioms YMGap.Continuum.SU2CharacterFusionSynthesis.synthesis_fusionPacket_product
#print axioms YMGap.Continuum.SU2CharacterFusionSynthesis.polynomialFusionProduct_eq_pmul
