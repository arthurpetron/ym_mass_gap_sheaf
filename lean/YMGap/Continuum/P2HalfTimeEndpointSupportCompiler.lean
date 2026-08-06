/-
Track 11.7-fusion / R4z -- all-depth endpoint-support compiler.

For `m <= N`, reversing the cutoff-square coordinates by

    i = N-a,  j = N-b

turns the Clebsch support at channel `2*N-m` into the parity triangle

    i+j <= m,  i+j+m even.

This module proves that reindexing once for every depth.  Combined with the
successive-increment prefix semantics from
`P2HalfTimeEndpointRatioCertificateCompiler`, it identifies the physical box
sum with the same reflected endpoint expression consumed by the ratio
compiler.  Thus future endpoint shells no longer require handwritten support
tables or one theorem per active boundary pair.

No `Classical`, `native_decide`, `sorry`, custom axiom, or noncomputable
declaration.
-/

import YMGap.Continuum.FusionStrandExactReindex
import YMGap.Continuum.P2HalfTimeEndpointRatioCertificateCompiler

namespace YMGap.Continuum.P2HalfTimeEndpointSupportCompiler

set_option maxRecDepth 100000
set_option maxHeartbeats 360000

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.BondMovingStep
open YMGap.Continuum.CubeRatioBounds
open YMGap.Continuum.FusionQuotientCollapse
open YMGap.Continuum.HeatKernelRGStep
open YMGap.Continuum.P2HalfTimeEndpointRatioCertificateCompiler
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.SelfFusionLogConcave

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. Generic finite-sum reversal and truncation -/

private theorem fsum_shift_cons_local (g : Nat -> Q') :
    forall n, fsum g (n + 1) ≈ g 0 + fsum (fun i => g (i + 1)) n
  | 0 => by
      refine Q'.eqv_trans _ _ _ (Q'.eqv_of_eq (Q'.zero_add' (g 0))) ?_
      exact Q'.eqv_symm (Q'.eqv_of_eq (Q'.add_zero' (g 0)))
  | n + 1 => by
      refine Q'.eqv_trans _ _ _
        (Q'.add_eqv_congr_right _ _ _ (fsum_shift_cons_local g n)) ?_
      exact Q'.add_assoc_eqv _ _ _

private theorem fsum_reverse_local (G : Nat -> Q') :
    forall n, fsum (fun i => G (n - i)) (n + 1) ≈ fsum G (n + 1)
  | 0 => Q'.eqv_refl _
  | n + 1 => by
      refine Q'.eqv_trans _ _ _
        (fsum_shift_cons_local (fun i => G ((n + 1) - i)) (n + 1)) ?_
      have htail :
          fsum (fun i => G ((n + 1) - (i + 1))) (n + 1) ≈
            fsum (fun i => G (n - i)) (n + 1) := by
        apply fsum_eqv_congr
        intro i
        exact Q'.eqv_of_eq (congrArg G (by omega))
      refine Q'.eqv_trans _ (G (n + 1) + fsum G (n + 1)) _
        (Q'.add_eqv_congr_left _ _ _
          (Q'.eqv_trans _ _ _ htail (fsum_reverse_local G n))) ?_
      exact Q'.add_comm_eqv _ _

private theorem fsum_zero_extension {f : Nat -> Q'} {n m : Nat}
    (hnm : n <= m) (hz : forall i, n <= i -> f i ≈ 0) :
    fsum f m ≈ fsum f n := by
  induction hnm with
  | refl => exact Q'.eqv_refl _
  | @step m hnm ih =>
      rw [fsum_succ]
      exact Q'.eqv_trans _ (fsum f n + 0) _
        (Q'.add_eqv_congr' ih (hz m hnm))
        (Q'.eqv_of_eq (Q'.add_zero' _))

/-! ## 2. Reflected endpoint semantics as an ordinary finite box -/

/-- Coefficients read inward from the cutoff boundary. -/
def endpointCoefficient (w : Q') (N i : Nat) : Q' :=
  coeffW w (N - i)

/-- The successive-increment environment for the reversed endpoint string. -/
def endpointIncrementEnvironment (w : Q') (N : Nat) : Nat -> Q' :=
  incrementEnvironment (endpointCoefficient w N)

/-- Reflected endpoint box consumed by the ratio compiler. -/
def endpointBoxExpr (w : Q') (N m : Nat) : Q' :=
  eval (endpointIncrementEnvironment w N) (endpointTriangleExpr m)

/-- Direct ordered parity-triangle term after reversing cutoff coordinates. -/
def endpointDirectTerm (w : Q') (N m i j : Nat) : Q' :=
  if endpointPairActive m i j then
    endpointCoefficient w N i * endpointCoefficient w N j
  else 0

/-- Direct finite parity-triangle box. -/
def endpointDirectBox (w : Q') (N m : Nat) : Q' :=
  fsum (fun i => fsum (endpointDirectTerm w N m i) (m + 1)) (m + 1)

private theorem eval_polyFsum_eq_fsum
    (rho : Nat -> Q') (f : Nat -> PolyExpr) : forall n,
    eval rho (polyFsum f n) = fsum (fun i => eval rho (f i)) n
  | 0 => rfl
  | n + 1 => by
      change eval rho (polyFsum f n) + eval rho (f n) =
        fsum (fun i => eval rho (f i)) n + eval rho (f n)
      rw [eval_polyFsum_eq_fsum rho f n]

/-- The reflected expression evaluates to the direct parity-triangle box. -/
theorem endpointDirectBox_eq_endpointBoxExpr (w : Q') (N m : Nat) :
    endpointDirectBox w N m ≈ endpointBoxExpr w N m := by
  unfold endpointDirectBox endpointDirectTerm endpointBoxExpr endpointTriangleExpr
  rw [eval_polyFsum_eq_fsum]
  apply fsum_eqv_congr
  intro i
  rw [eval_polyFsum_eq_fsum]
  apply fsum_eqv_congr
  intro j
  by_cases hactive : endpointPairActive m i j = true
  · simp only [hactive, if_true, eval]
    refine Q'.eqv_trans _
      (eval (endpointIncrementEnvironment w N) (endpointPrefixExpr i) *
        endpointCoefficient w N j) _
      (Q'.mul_eqv_congr_right _ _ _
        (Q'.eqv_symm
          (eval_endpointPrefixExpr_incrementEnvironment
            (endpointCoefficient w N) i))) ?_
    exact Q'.mul_eqv_congr_left _ _ _
      (Q'.eqv_symm
        (eval_endpointPrefixExpr_incrementEnvironment
          (endpointCoefficient w N) j))
  · have hfalse : endpointPairActive m i j = false :=
      Bool.eq_false_iff.mpr hactive
    simp only [hfalse, Bool.false_eq_true, if_false, eval]
    exact Q'.eqv_refl 0

/-! ## 3. Clebsch support equals the parity triangle -/

private theorem endpointPairActive_true_iff (m i j : Nat) :
    endpointPairActive m i j = true <->
      i + j <= m /\ (i + j + m) % 2 = 0 := by
  simp only [endpointPairActive, decide_eq_true_eq]

private theorem fusionInd_reversed_endpoint
    (N m i j : Nat) (hmN : m <= N) (hiN : i <= N) (hjN : j <= N) :
    fusionInd (N - i) (N - j) (2 * N - m) =
      if endpointPairActive m i j then (1 : Q') else 0 := by
  by_cases hactive : endpointPairActive m i j = true
  · have hp := (endpointPairActive_true_iff m i j).mp hactive
    have hok : fusionOK (N - i) (N - j) (2 * N - m) = true := by
      rw [fusionOK_eq_true_iff]
      constructor
      · rcases Nat.le_total (N - i) (N - j) with hij | hji
        · simp only [Nat.max_eq_right hij, Nat.min_eq_left hij]
          omega
        · simp only [Nat.max_eq_left hji, Nat.min_eq_right hji]
          omega
      · constructor
        · omega
        · omega
    unfold fusionInd
    simp only [hok, hactive, if_true]
  · have hfalse : endpointPairActive m i j = false :=
      Bool.eq_false_iff.mpr hactive
    have hokFalse : fusionOK (N - i) (N - j) (2 * N - m) = false := by
      apply Bool.eq_false_iff.mpr
      intro hok
      rcases (fusionOK_eq_true_iff _ _ _).mp hok with ⟨_, hsum, hpar⟩
      have hp : i + j <= m /\ (i + j + m) % 2 = 0 := by
        constructor <;> omega
      exact hactive ((endpointPairActive_true_iff m i j).mpr hp)
    unfold fusionInd
    simp only [hokFalse, hfalse, Bool.false_eq_true, if_false]

private theorem reversedBoxTerm_eq_endpointDirectTerm
    (w : Q') (N m i j : Nat) (hmN : m <= N)
    (hiN : i <= N) (hjN : j <= N) :
    fusionInd (N - i) (N - j) (2 * N - m) *
        (coeffW w (N - i) * coeffW w (N - j)) ≈
      endpointDirectTerm w N m i j := by
  rw [fusionInd_reversed_endpoint N m i j hmN hiN hjN]
  unfold endpointDirectTerm endpointCoefficient
  by_cases hactive : endpointPairActive m i j = true
  · simp only [hactive, if_true]
    exact Q'.one_mul_eqv _
  · have hfalse : endpointPairActive m i j = false :=
      Bool.eq_false_iff.mpr hactive
    simp only [hfalse, Bool.false_eq_true, if_false]
    exact Q'.zero_mul_eqv _

private theorem endpointDirectTerm_zero_right
    (w : Q') (N m i j : Nat) (hj : m + 1 <= j) :
    endpointDirectTerm w N m i j ≈ 0 := by
  have hfalse : endpointPairActive m i j = false := by
    apply Bool.eq_false_iff.mpr
    intro hactive
    have hp := (endpointPairActive_true_iff m i j).mp hactive
    omega
  unfold endpointDirectTerm
  rw [hfalse]
  exact Q'.eqv_refl 0

private theorem endpointDirectTerm_zero_left
    (w : Q') (N m i j : Nat) (hi : m + 1 <= i) :
    endpointDirectTerm w N m i j ≈ 0 := by
  have hfalse : endpointPairActive m i j = false := by
    apply Bool.eq_false_iff.mpr
    intro hactive
    have hp := (endpointPairActive_true_iff m i j).mp hactive
    omega
  unfold endpointDirectTerm
  rw [hfalse]
  exact Q'.eqv_refl 0

/-- The cutoff-square box at distance `m` from the top is exactly the direct
ordered parity triangle.  This theorem performs all reversal and zero-tail
elimination generically. -/
theorem boxSum_top_endpointDirect (w : Q') (N m : Nat) (hmN : m <= N) :
    boxSum w N (2 * N - m) ≈ endpointDirectBox w N m := by
  let kernel := fun a b => fusionInd a b (2 * N - m) *
    (coeffW w a * coeffW w b)
  have hreverse :
      boxSum w N (2 * N - m) ≈
        fsum (fun i => fsum (fun j => kernel (N - i) (N - j)) (N + 1))
          (N + 1) := by
    unfold boxSum
    refine Q'.eqv_trans _
      (fsum (fun i => fsum (fun b => kernel (N - i) b) (N + 1))
        (N + 1)) _
      (Q'.eqv_symm
        (fsum_reverse_local
          (fun a => fsum (fun b => kernel a b) (N + 1)) N)) ?_
    apply fsum_eqv_congr
    intro i
    exact Q'.eqv_symm
      (fsum_reverse_local (fun b => kernel (N - i) b) N)
  have hterms :
      fsum (fun i => fsum (fun j => kernel (N - i) (N - j)) (N + 1))
          (N + 1) ≈
        fsum (fun i => fsum (endpointDirectTerm w N m i) (N + 1))
          (N + 1) := by
    apply fsum_eqv_congr_lt
    intro i hi
    apply fsum_eqv_congr_lt
    intro j hj
    exact reversedBoxTerm_eq_endpointDirectTerm w N m i j hmN
      (by omega) (by omega)
  have hinner :
      fsum (fun i => fsum (endpointDirectTerm w N m i) (N + 1))
          (N + 1) ≈
        fsum (fun i => fsum (endpointDirectTerm w N m i) (m + 1))
          (N + 1) := by
    apply fsum_eqv_congr
    intro i
    exact fsum_zero_extension (by omega)
      (fun j hj => endpointDirectTerm_zero_right w N m i j hj)
  have houter :
      fsum (fun i => fsum (endpointDirectTerm w N m i) (m + 1))
          (N + 1) ≈ endpointDirectBox w N m := by
    unfold endpointDirectBox
    apply fsum_zero_extension (by omega)
    intro i hi
    apply fsum_zero_below
    intro j _
    exact endpointDirectTerm_zero_left w N m i j hi
  exact Q'.eqv_trans _ _ _ hreverse
    (Q'.eqv_trans _ _ _ hterms (Q'.eqv_trans _ _ _ hinner houter))

/-- **All-depth top-shell support compiler.**  Every physical endpoint box is
the reflected parity triangle used by the adjacent-depth ratio compiler. -/
theorem boxSum_top_endpoint (w : Q') (N m : Nat) (hmN : m <= N) :
    boxSum w N (2 * N - m) ≈ endpointBoxExpr w N m :=
  Q'.eqv_trans _ _ _ (boxSum_top_endpointDirect w N m hmN)
    (endpointDirectBox_eq_endpointBoxExpr w N m)

end YMGap.Continuum.P2HalfTimeEndpointSupportCompiler

/-! ## Axiom-dependency gates -/

#print axioms YMGap.Continuum.P2HalfTimeEndpointSupportCompiler.endpointDirectBox_eq_endpointBoxExpr
#print axioms YMGap.Continuum.P2HalfTimeEndpointSupportCompiler.boxSum_top_endpointDirect
#print axioms YMGap.Continuum.P2HalfTimeEndpointSupportCompiler.boxSum_top_endpoint
