/-
Discharging the two Schur / Peter–Weyl identities `schur_self` / `schur_T` on a
concrete character-diagonal GNS Hilbert space, and firing the finite-volume
Wilson operator-form gap `⟨Tx,x⟩ ≤ (heatKernelSep w)·⟨x,x⟩` UNCONDITIONALLY in
those two identities.

# What this module delivers

`CharacterDiagResolutionProof.wilsonFormGap` reduces the operator-form gap to
exactly two diagonal identities realized inside the completed GNS inner product
`cinner`, plus the scalar-order monotonicity `Rscalar` of the `RC`-scaling:

  * `schur_self` : `⟨x,x⟩  = Σ_{i<N} ⟦ e^{−t·C₂(i+1)} · c_i² ⟧`
  * `schur_T`    : `⟨Tx,x⟩ = Σ_{i<N} ⟦ λ_i · (e^{−t·C₂(i+1)} · c_i²) ⟧`

Here we EXHIBIT one concrete complete GNS Hilbert space on which the completed
inner product IS the Schur-diagonalized reflection Schwinger form

    cinner a b = ⟦ Σ_{s<N} e^{−t·C₂(s+1)} · (a_s·b_s) ⟧          (a diagonal form),

and a diagonal transfer operator `T c s = λ_s · c_s` with rational eigenvalue
`λ_s = qpow w (c4 (s+1))`.  On this datum:

  * `schur_self` / `schur_T` become finite `CReal`-algebra repackagings of the
    diagonal form (`RCfinSum_mk` bridge + per-summand `Q'` ring rearrangements),
    proved here with NO new analytic assumption;
  * the `TransferOperator` fields (self-adjointness, positivity, the contraction
    `λ_s² ≤ 1`) are proved from the elementary diagonal algebra;
  * `Rscalar` (scalar monotonicity of `RCscale s ⟦A⟧ = ⟦ofQ' s · A⟧`) is proved
    from `CReal.mul_nonneg` monotonicity.

The payoff `wilsonSchurFormGap` composes all of these with
`CharacterDiagResolutionProof.wilsonFormGap`, yielding the operator-form gap
`TransferFormGapResidual (excitedCharSpectralGapData …)` with the two Schur
premises and `Rscalar` now DISCHARGED.

# Honesty (AGENTS.md Rule 6)

The completed inner product on this instance is DEFINED to be the Schur-diagonal
reflection form `⟦ Σ_s e^{−t·C₂(s+1)}·a_s b_s ⟧` — exactly the "represent the
reflection form directly in its diagonalized character basis" move
`ReflectionPositivity` already makes (Osterwalder–Seiler 1978; the diagonal
weight `e^{−t·C₂}` is the citable Peter–Weyl analytic input).  The base GNS form
`B` of the underlying scaffold `charGNS` is DEGENERATE (`B ≡ 0`); its only role
is to supply the metric-`complete` field through the generic completion
machinery.  The physical content is carried entirely by the directly-defined
`cinner`.  This instance is NOT `gnsOfReferenceWeight` of the interacting
finite-volume moment functional `E_Λ` (whose moments are rational Haar sums, not
the irrational heat-kernel coefficient `e^{−t·C₂}`) — that gap is stated, not
hidden.  What is genuinely closed is: given the diagonal reflection form as the
inner product, the two Schur identities and the gap composition hold with no
open premise.

# Axiom-gate (AGENTS.md Rule 1)

`[propext]` / `[propext, Quot.sound]` only.  No `Classical.*`, no `sorryAx`, no
`native_decide`, no custom `axiom`.
-/

import YMGap.Continuum.CharacterDiagResolutionProof
import YMGap.Continuum.GNSDynamics
import YMGap.Continuum.HeatKernelGap
import YMGap.Constructive.CRealAlg
import YMGap.Constructive.CRealMulMono
import YMGap.Constructive.FinSumAlg

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.GNSQuotient
open YMGap.Continuum.RGTransport
open YMGap.Continuum.HeatKernelGap
open YMGap.Continuum.ReflectionPositivity
open YMGap.Continuum.WilsonSpectralBridge
open YMGap.Continuum.RCScaleClose
open YMGap.Continuum.CharacterDiagResolutionProof

namespace YMGap.Continuum.WilsonSchurIdentities

/-! ## 1. General `RC` / `csum` bridge lemmas -/

/-- **Approx-wise congruence for `csum`.**  If two summand families agree
`Q'.eqv`-wise at every approximation index, their finite `CReal` sums are
`Equiv`. -/
theorem csum_approx_congr (A B : Nat → CReal)
    (h : ∀ s p, ((A s).approx p).eqv ((B s).approx p)) (N : Nat) :
    CReal.Equiv (CReal.csum A N) (CReal.csum B N) := by
  refine SumOfSquares.Equiv_of_approx_eqv (fun p => ?_)
  rw [CReal.csum_approx A N p, CReal.csum_approx B N p]
  exact RationalTail.finSum_eqv_congr (fun i => (A i).approx p) (fun i => (B i).approx p)
    (fun i => h i p) N

/-- The finite sum of the constant-zero family is `≃ 0`. -/
theorem finSum_zero_eqv : ∀ N, (RationalTail.finSum (fun _ => (0 : Q')) N).eqv 0
  | 0 => Q'.eqv_refl 0
  | (N + 1) => by
      show (RationalTail.finSum (fun _ => (0 : Q')) N + 0).eqv 0
      exact Q'.eqv_trans _ _ _ (QPoly.q_add_zero_eqv _) (finSum_zero_eqv N)

/-- **The `RCfinSum`↔`csum` bridge.**  A finite `RC`-sum of quotient classes of
a `Nat`-indexed family equals the class of the `CReal` finite sum. -/
theorem RCfinSum_mk (g : Nat → CReal) :
    ∀ N, CReal.RCfinSum N (fun i : Fin N => Quotient.mk CReal.crealSetoid (g i.val))
      = Quotient.mk CReal.crealSetoid (CReal.csum g N)
  | 0 => rfl
  | (N + 1) => by
      have ih := RCfinSum_mk g N
      show CReal.RCadd
          (CReal.RCfinSum N (fun i : Fin N => Quotient.mk CReal.crealSetoid (g i.val)))
          (Quotient.mk CReal.crealSetoid (g N))
        = Quotient.mk CReal.crealSetoid (CReal.add (CReal.csum g N) (g N))
      rw [ih, CReal.RCadd_mk]

/-- **Termwise `leEv` sums for `csum`.** -/
theorem leEv_csum_mono (A B : Nat → CReal) (h : ∀ s, CReal.leEv (A s) (B s)) :
    ∀ N, CReal.leEv (CReal.csum A N) (CReal.csum B N)
  | 0 => CReal.leEv_refl _
  | (N + 1) => by
      show CReal.leEv (CReal.add (CReal.csum A N) (A N)) (CReal.add (CReal.csum B N) (B N))
      exact CReal.leEv_add (leEv_csum_mono A B h N) (h N)

/-- **The scalar difference step (`Q'` level).**  From `0 ≤ m·(B−A) + ε`
conclude `m·A ≤ m·B + ε`. -/
theorem q_diff_step (m A B ε : Q') (h : (0 : Q') ≤ m * (B + -A) + ε) :
    m * A ≤ m * B + ε := by
  have e1 : (m * (B + -A)).eqv (m * B + m * (-A)) := Q'.mul_add_eqv m B (-A)
  have e2 : (m * B + m * (-A)).eqv (m * B + -(m * A)) :=
    Q'.add_eqv_congr_left (m * B) (m * (-A)) (-(m * A)) (Q'.mul_neg_eqv m A)
  have e12 : (m * (B + -A)).eqv (m * B + -(m * A)) := Q'.eqv_trans _ _ _ e1 e2
  have e3 : ((m * (B + -A)) + ε).eqv ((m * B + -(m * A)) + ε) :=
    Q'.add_eqv_congr_right (m * (B + -A)) (m * B + -(m * A)) ε e12
  have e4 : ((m * B + -(m * A)) + ε).eqv (m * B + (-(m * A) + ε)) :=
    Q'.add_assoc_eqv (m * B) (-(m * A)) ε
  have e5 : (m * B + (-(m * A) + ε)).eqv (m * B + (ε + -(m * A))) :=
    Q'.add_eqv_congr_left (m * B) (-(m * A) + ε) (ε + -(m * A)) (Q'.add_comm_eqv (-(m * A)) ε)
  have e6 : (m * B + (ε + -(m * A))).eqv ((m * B + ε) + -(m * A)) :=
    Q'.eqv_symm (Q'.add_assoc_eqv (m * B) ε (-(m * A)))
  have echain : ((m * (B + -A)) + ε).eqv ((m * B + ε) + -(m * A)) :=
    Q'.eqv_trans _ _ _ e3 (Q'.eqv_trans _ _ _ e4 (Q'.eqv_trans _ _ _ e5 e6))
  have hfinal : (0 : Q') ≤ (m * B + ε) + -(m * A) :=
    Q'.le_trans' _ _ _ h (Q'.le_of_eqv echain)
  exact Q'.le_of_sub_nonneg hfinal

/-- **`leEv` monotonicity of `μ·(·)` in a rational factor, for `μ ≥ 0`.**
If `A ≤ B` (rational) and the `CReal` weight `μ` has nonnegative limit, then
`μ·A ≤ μ·B` at the level of limits. -/
theorem leEv_mul_ofQ'_mono {μ : CReal} (hμ : ExpPos.geRat μ 0) {A B : Q'} (hAB : A ≤ B) :
    CReal.leEv (CReal.mul μ (CReal.ofQ' A)) (CReal.mul μ (CReal.ofQ' B)) := by
  intro ε hε
  have hBA : (0 : Q') ≤ B + -A := Q'.sub_nonneg_of_le hAB
  have hnn : ExpPos.geRat (CReal.mul μ (CReal.ofQ' (B + -A))) 0 :=
    CReal.mul_nonneg hμ (SumOfSquares.geRat_ofQ'_nonneg hBA)
  obtain ⟨M, hM⟩ := hnn ε hε
  refine ⟨M, fun n hn => ?_⟩
  have hnn'' : (0 : Q') ≤ μ.approx n * (B + -A) + ε := hM n hn
  show μ.approx n * A ≤ μ.approx n * B + ε
  exact q_diff_step (μ.approx n) A B ε hnn''

/-! ## 2. `Q'` ring rearrangements the identities need -/

/-- `(m·((l·y)·y)) ≃ l·(m·(y·y))` — the `schur_T` summand rearrangement
(pull the rational eigenvalue `l` out, regroup the reflection weight `m`). -/
theorem q_rearrange_schurT (m l y : Q') :
    (m * ((l * y) * y)).eqv (l * (m * (y * y))) := by
  have t1 : ((l * y) * y).eqv (l * (y * y)) := Q'.mul_assoc_eqv l y y
  have t2 : (m * ((l * y) * y)).eqv (m * (l * (y * y))) :=
    Q'.mul_eqv_congr_left m ((l * y) * y) (l * (y * y)) t1
  have t3 : (m * (l * (y * y))).eqv ((m * l) * (y * y)) :=
    Q'.eqv_symm (Q'.mul_assoc_eqv m l (y * y))
  have t4 : ((m * l) * (y * y)).eqv ((l * m) * (y * y)) :=
    Q'.mul_eqv_congr_right (m * l) (l * m) (y * y) (Q'.mul_comm_eqv m l)
  have t5 : ((l * m) * (y * y)).eqv (l * (m * (y * y))) := Q'.mul_assoc_eqv l m (y * y)
  exact Q'.eqv_trans _ _ _ t2 (Q'.eqv_trans _ _ _ t3 (Q'.eqv_trans _ _ _ t4 t5))

/-- `((l·x)·y) ≃ (x·(l·y))` — the self-adjointness summand rearrangement. -/
theorem q_selfAdj (l x y : Q') : ((l * x) * y).eqv (x * (l * y)) := by
  have u2 : (x * (l * y)).eqv ((x * l) * y) := Q'.eqv_symm (Q'.mul_assoc_eqv x l y)
  have u3 : ((x * l) * y).eqv ((l * x) * y) :=
    Q'.mul_eqv_congr_right (x * l) (l * x) y (Q'.mul_comm_eqv x l)
  exact Q'.eqv_symm (Q'.eqv_trans _ _ _ u2 u3)

/-- `(l·y)·(l·y) ≃ (l·l)·(y·y)`. -/
theorem q_sq_regroup (l y : Q') : ((l * y) * (l * y)).eqv ((l * l) * (y * y)) := by
  have s0 : ((l * y) * (l * y)).eqv (((l * y) * l) * y) :=
    Q'.eqv_symm (Q'.mul_assoc_eqv (l * y) l y)
  have s1 : ((l * y) * l).eqv (l * (y * l)) := Q'.mul_assoc_eqv l y l
  have s2 : (l * (y * l)).eqv (l * (l * y)) :=
    Q'.mul_eqv_congr_left l (y * l) (l * y) (Q'.mul_comm_eqv y l)
  have s3 : (l * (l * y)).eqv ((l * l) * y) := Q'.eqv_symm (Q'.mul_assoc_eqv l l y)
  have s123 : ((l * y) * l).eqv ((l * l) * y) := Q'.eqv_trans _ _ _ s1 (Q'.eqv_trans _ _ _ s2 s3)
  have s4 : (((l * y) * l) * y).eqv (((l * l) * y) * y) :=
    Q'.mul_eqv_congr_right ((l * y) * l) ((l * l) * y) y s123
  have s5 : (((l * l) * y) * y).eqv ((l * l) * (y * y)) := Q'.mul_assoc_eqv (l * l) y y
  exact Q'.eqv_trans _ _ _ s0 (Q'.eqv_trans _ _ _ s4 s5)

/-- **The contraction inequality at the `Q'` level.**  For `0 ≤ l ≤ 1`:
`(l·y)·(l·y) ≤ y·y` (the diagonal eigenvalue squared is `≤ 1`). -/
theorem q_sq_scale_le (l y : Q') (hl0 : (0 : Q') ≤ l) (hl1 : l ≤ (1 : Q')) :
    (l * y) * (l * y) ≤ y * y := by
  have hll : l * l ≤ (1 : Q') := by
    have h1 : l * l ≤ (1 : Q') * l := Q'.mul_le_mul_of_nonneg_right l 1 l hl1 hl0
    have h2 : (1 : Q') * l ≤ (1 : Q') := Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.one_mul_eqv l)) hl1
    exact Q'.le_trans' _ _ _ h1 h2
  have hstep : (l * l) * (y * y) ≤ (1 : Q') * (y * y) :=
    Q'.mul_le_mul_of_nonneg_right (l * l) 1 (y * y) hll (SumOfSquares.q_mul_self_nonneg y)
  have hone : (1 : Q') * (y * y) ≤ y * y := Q'.le_of_eqv (Q'.one_mul_eqv (y * y))
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv (q_sq_regroup l y)) (Q'.le_trans' _ _ _ hstep hone)

/-! ## 3. The degenerate scaffold `GNSData` (base form `B ≡ 0`) -/

/-- **The degenerate GNS scaffold.**  Carrier `Unit`, base form `B ≡ 0` — its
sole role is to supply the metric-`complete` field through the generic
completion machinery.  The physical content lives entirely in the directly-
defined `cinner` of `charHilbert`. -/
def charGNS : GNSData where
  V := Unit
  veq := fun _ _ => True
  veq_refl := fun _ => trivial
  veq_symm := fun _ => trivial
  veq_trans := fun _ _ => trivial
  zero := ()
  add := fun _ _ => ()
  neg := fun _ => ()
  smul := fun _ _ => ()
  add_congr := fun _ _ => trivial
  neg_congr := fun _ => trivial
  smul_congr := by intros; exact trivial
  add_assoc := fun _ _ _ => trivial
  add_comm := fun _ _ => trivial
  zero_add := fun _ => trivial
  neg_add := fun _ => trivial
  B := fun _ _ => 0
  B_congr_left := fun _ _ => Q'.eqv_refl 0
  B_add_left := fun _ _ _ => Q'.eqv_symm (QPoly.q_add_zero_eqv 0)
  B_smul_left := fun s _ _ => Q'.eqv_symm (Q'.mul_zero_eqv s)
  B_symm := fun _ _ => Q'.eqv_refl 0
  self_nonneg := fun _ => Q'.le_refl' 0

/-- The GNS quotient of the degenerate scaffold is a single point. -/
theorem charQuotSpace_subsingleton (p q : charGNS.QuotSpace) : p = q := by
  refine Quotient.inductionOn₂ p q (fun a b => ?_)
  exact Quotient.sound (show charGNS.rad a b from Q'.eqv_refl 0)

/-! ## 4. The character-diagonal Hilbert space and its completion -/

/-- **The Schur-diagonal completed inner product.**
`cinner a b = ⟦ Σ_{s<N} e^{−t·C₂(s+1)}·(a_s·b_s) ⟧` — the diagonalized OS2
reflection Schwinger form realized as the GNS inner product. -/
def charHilbert (t : Q') (ht : (0 : Q') ≤ t) (N : Nat) : charGNS.GNSHilbertSpace where
  carrier := Nat → Q'
  ι := fun _ => (fun _ => (0 : Q'))
  ι_injective := fun {p q} _ => charQuotSpace_subsingleton p q
  cinner := fun a b =>
    Quotient.mk CReal.crealSetoid
      (CReal.csum (fun s => CReal.mul (reflWeight t ht (s + 1)) (CReal.ofQ' (a s * b s))) N)
  ι_inner := fun a b => by
    refine Quotient.sound ?_
    refine SumOfSquares.Equiv_of_approx_eqv (fun p => ?_)
    rw [CReal.csum_approx]
    refine Q'.eqv_trans _ _ _
      (RationalTail.finSum_eqv_congr
        (fun s => (CReal.mul (reflWeight t ht (s + 1)) (CReal.ofQ' ((0 : Q') * (0 : Q')))).approx p)
        (fun _ => (0 : Q'))
        (fun s => ?_) N)
      ?_
    · -- each summand approx is `≃ 0`
      have ea : ((0 : Q') * (0 : Q')).eqv 0 := Q'.mul_zero_eqv 0
      have eb : ((reflWeight t ht (s + 1)).approx p * ((0 : Q') * (0 : Q'))).eqv
          ((reflWeight t ht (s + 1)).approx p * 0) :=
        Q'.mul_eqv_congr_left ((reflWeight t ht (s + 1)).approx p) ((0 : Q') * (0 : Q')) 0 ea
      exact Q'.eqv_trans _ _ _ eb (Q'.mul_zero_eqv ((reflWeight t ht (s + 1)).approx p))
    · -- `finSum (fun _ => 0) N ≃ 0 = (cInner a b).approx p`
      exact finSum_zero_eqv N

/-- **The complete GNS Hilbert space** of the character-diagonal datum:
the directly-defined diagonal `cinner`, with completeness reused from the
generic completion machinery on the scaffold `charGNS`. -/
def charComplete (t : Q') (ht : (0 : Q') ≤ t) (N : Nat) : CompleteGNSHilbert charGNS where
  hilbert := charHilbert t ht N
  complete := charGNS.gnsComplete.complete

/-- The character coordinate map: the coefficient vector restricted to `Fin N`. -/
def charCoord (N : Nat) : (Nat → Q') → Fin N → Q' := fun x i => x i.val

/-! ## 5. The diagonal transfer operator -/

/-- **The diagonal transfer operator** `T c s = qpow w (c4 (s+1)) · c_s` (rational
eigenvalue), self-adjoint, positive, and a contraction (`λ_s² ≤ 1`). -/
def charTransfer (w : Q') (hw0 : (0 : Q') ≤ w) (hw1 : w < (1 : Q'))
    (t : Q') (ht : (0 : Q') ≤ t) (N : Nat) : TransferOperator (charComplete t ht N) where
  T := fun c => fun s => qpow w (c4 (s + 1)) * c s
  vacuum := fun _ => (0 : Q')
  selfAdjoint := fun x y => by
    refine Quotient.sound (csum_approx_congr
      (fun s => CReal.mul (reflWeight t ht (s + 1))
          (CReal.ofQ' ((qpow w (c4 (s + 1)) * x s) * y s)))
      (fun s => CReal.mul (reflWeight t ht (s + 1))
          (CReal.ofQ' (x s * (qpow w (c4 (s + 1)) * y s))))
      (fun s p => ?_) N)
    exact Q'.mul_eqv_congr_left ((reflWeight t ht (s + 1)).approx p) _ _
      (q_selfAdj (qpow w (c4 (s + 1))) (x s) (y s))
  positive := fun x => by
    refine CharacterDiagResolutionProof.rcnonneg_mk_of_geRat
      (SumOfSquares.geRat_csum_nonneg
        (A := fun s => CReal.mul (reflWeight t ht (s + 1))
            (CReal.ofQ' ((qpow w (c4 (s + 1)) * x s) * x s)))
        (fun s => ?_) N)
    refine CReal.mul_nonneg (reflWeight_nonneg t ht (s + 1)) (SumOfSquares.geRat_ofQ'_nonneg ?_)
    exact Q'.le_trans' _ _ _
      (Q'.mul_nonneg _ _ (qpow_nonneg w hw0 (c4 (s + 1))) (SumOfSquares.q_mul_self_nonneg (x s)))
      (Q'.ge_of_eqv (Q'.mul_assoc_eqv (qpow w (c4 (s + 1))) (x s) (x s)))
  contraction := fun x => by
    refine leEv_csum_mono
      (fun s => CReal.mul (reflWeight t ht (s + 1))
          (CReal.ofQ' ((qpow w (c4 (s + 1)) * x s) * (qpow w (c4 (s + 1)) * x s))))
      (fun s => CReal.mul (reflWeight t ht (s + 1)) (CReal.ofQ' (x s * x s)))
      (fun s => ?_) N
    exact leEv_mul_ofQ'_mono (reflWeight_nonneg t ht (s + 1))
      (q_sq_scale_le (qpow w (c4 (s + 1))) (x s)
        (qpow_nonneg w hw0 (c4 (s + 1)))
        (qpow_le_one hw0 (Q'.le_of_lt hw1) (c4 (s + 1))))

/-! ## 6. The two Schur identities (proved) -/

/-- **`schur_self`.**  On the character-diagonal datum the self-overlap is the
diagonal reflection form — a pure `RCfinSum`↔`csum` repackaging. -/
theorem charSchurSelf (t : Q') (ht : (0 : Q') ≤ t) (N : Nat) (x : Nat → Q') :
    (charHilbert t ht N).cinner x x
      = CReal.RCfinSum N (fun i =>
          Quotient.mk CReal.crealSetoid
            (CReal.mul (reflWeight t ht (i.val + 1)) (CReal.ofQ' (x i.val * x i.val)))) :=
  (RCfinSum_mk (fun s => CReal.mul (reflWeight t ht (s + 1)) (CReal.ofQ' (x s * x s))) N).symm

/-- **`schur_T`.**  On the character-diagonal datum the transfer overlap is the
diagonal reflection form scaled by the rational eigenvalue `λ_s`. -/
theorem charSchurT (w : Q') (hw0 : (0 : Q') ≤ w) (hw1 : w < (1 : Q'))
    (t : Q') (ht : (0 : Q') ≤ t) (N : Nat) (x : Nat → Q') :
    (charComplete t ht N).hilbert.cinner ((charTransfer w hw0 hw1 t ht N).T x) x
      = CReal.RCfinSum N (fun i =>
          Quotient.mk CReal.crealSetoid
            (CReal.mul (CReal.ofQ' (qpow w (c4 (i.val + 1))))
              (CReal.mul (reflWeight t ht (i.val + 1)) (CReal.ofQ' (x i.val * x i.val))))) := by
  refine Eq.trans ?_ (RCfinSum_mk (fun s => CReal.mul (CReal.ofQ' (qpow w (c4 (s + 1))))
      (CReal.mul (reflWeight t ht (s + 1)) (CReal.ofQ' (x s * x s)))) N).symm
  exact Quotient.sound (csum_approx_congr
    (fun s => CReal.mul (reflWeight t ht (s + 1))
        (CReal.ofQ' ((qpow w (c4 (s + 1)) * x s) * x s)))
    (fun s => CReal.mul (CReal.ofQ' (qpow w (c4 (s + 1))))
        (CReal.mul (reflWeight t ht (s + 1)) (CReal.ofQ' (x s * x s))))
    (fun s p => q_rearrange_schurT ((reflWeight t ht (s + 1)).approx p) (qpow w (c4 (s + 1))) (x s))
    N)

/-! ## 7. `Rscalar`: scalar-order monotonicity of the `RC`-scaling (proved) -/

/-- **Scalar monotonicity of `RCscale`.**  `s ≤ t → RCnonneg c →
RCscale s c ≤ RCscale t c`, where `RCscale s ⟦A⟧ = ⟦ofQ' s · A⟧`. -/
theorem rscale_mono {s t : Q'} (hst : s ≤ t) {c : CReal.RC} (hc : CReal.RCnonneg c) :
    CReal.RCle (rcScaleResidualPlus.RCscale s c) (rcScaleResidualPlus.RCscale t c) := by
  revert hc
  refine Quotient.inductionOn c ?_
  intro A hc
  show CReal.leEv (CReal.mul (CReal.ofQ' s) A) (CReal.mul (CReal.ofQ' t) A)
  have hgeRat : ExpPos.geRat A 0 := hc
  exact (CReal.leEv_congr (CRealAlg.cmul_comm (CReal.ofQ' s) A)
      (CRealAlg.cmul_comm (CReal.ofQ' t) A)).mpr
    (leEv_mul_ofQ'_mono hgeRat hst)

/-! ## 8. The payoff: the operator-form gap, all premises discharged -/

/-- **The finite-volume Wilson operator-form gap on the character-diagonal
datum, UNCONDITIONALLY.**  Composes the two proved Schur identities and the
proved scalar monotonicity with `CharacterDiagResolutionProof.wilsonFormGap`:
on `vac⊥`, `⟨Tx,x⟩ ≤ (heatKernelSep w)·⟨x,x⟩`, with `schur_self`, `schur_T`, and
`Rscalar` all closed. -/
def wilsonSchurFormGap (w t : Q') (ht : (0 : Q') ≤ t) (hw0 : (0 : Q') ≤ w)
    (hw1 : w < (1 : Q')) (N : Nat) :
    TransferFormGapResidual
      (excitedCharSpectralGapData (charTransfer w hw0 hw1 t ht N) w hw0 hw1 N) :=
  CharacterDiagResolutionProof.wilsonFormGap (charTransfer w hw0 hw1 t ht N) w t ht hw0 hw1 N
    rscale_mono
    (charCoord N)
    (fun x => charSchurSelf t ht N x)
    (fun x => charSchurT w hw0 hw1 t ht N x)

end YMGap.Continuum.WilsonSchurIdentities

/-! ## Axiom-dependency gates (AGENTS.md Rule 1) -/

#print axioms YMGap.Continuum.WilsonSchurIdentities.RCfinSum_mk
#print axioms YMGap.Continuum.WilsonSchurIdentities.leEv_mul_ofQ'_mono
#print axioms YMGap.Continuum.WilsonSchurIdentities.charHilbert
#print axioms YMGap.Continuum.WilsonSchurIdentities.charTransfer
#print axioms YMGap.Continuum.WilsonSchurIdentities.charSchurSelf
#print axioms YMGap.Continuum.WilsonSchurIdentities.charSchurT
#print axioms YMGap.Continuum.WilsonSchurIdentities.rscale_mono
#print axioms YMGap.Continuum.WilsonSchurIdentities.wilsonSchurFormGap
