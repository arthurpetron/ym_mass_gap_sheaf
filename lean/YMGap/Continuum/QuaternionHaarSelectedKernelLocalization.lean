/-
# Selected-link localization for ORIGINAL finite quaternion Haar

One literal ((1+x_(4*b))/2)^m factor is placed at every occurrence of b.
For a distinct in-carrier schedule, its actual selected-block projection
has the constant one-link moment to the schedule length, at every remaining
assignment. In-place projection retains zero-padded monomial aliases, so
the constant pin is pointwise, not an unjustified raw coefficient equality.
This supplies a finite conditional localization mass only. It assumes no
independence of original action factors, interacting conditional law,
typical raw-link chart, relative response, or physical survival estimate.
-/

import YMGap.Continuum.QuaternionHaarTensorLocalization
import YMGap.Continuum.SU2QuaternionHaarFamilyProjection
import YMGap.Continuum.SU2QuaternionHeadBlockLocality
import YMGap.Continuum.SU2QuaternionDisjointBlockHaarFactorization
import YMGap.Continuum.SU2QuaternionHaarKernelBound
import YMGap.Continuum.SU2MultiLinkHaarFactorization
import YMGap.Continuum.QPolyHaarPositiveSubstitution

namespace YMGap.Continuum.QuaternionHaarSelectedKernelLocalization

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.HalfPow (half)
open YMGap.RepTheory.RationalQuaternion (UnitNorm)
open YMGap.RepTheory.RationalQuaternionFourKernelProduct (base)
open YMGap.Continuum.RingNormaliser (evalMono evalMonoFrom)
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4CompactActionCPOrder (supported_polyMul)
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeHaarEndpoint
  (quaternionHaar_extend_supported_endpoint)
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity (SupportedQuaternionBlocks)
open YMGap.Continuum.SU2QuaternionWilsonWeightSOS
  (evalRatPoly_one evalRatPoly_var evalRatPoly_smul)
open YMGap.Continuum.SU2QuaternionPolynomialKernelConcentration
open YMGap.Continuum.SU2QuaternionKernelMomentLower
open YMGap.Continuum.SU2QuaternionPartialFactorizedHaar
open YMGap.Continuum.SU2QuaternionAuxiliaryLiftAlgebra (lift_supported)
open YMGap.Continuum.SU2QuaternionHaarKernelBound (haar_liftBoundary)
open YMGap.Continuum.SU2QuaternionBlockLocality
open YMGap.Continuum.SU2QuaternionOriginalHaarBlockMarginal
open YMGap.Continuum.SU2QuaternionHaarFamilyProjection
open YMGap.Continuum.SU2QuaternionDisjointBlockHaarFactorization (BlockDisjoint haar_product)
open YMGap.Continuum.SU2MultiLinkHaarFactorization
  (exponentAt_drop exponentAt_of_length_le allZero_iff prefix_congr)
open YMGap.Continuum.QuaternionHaarSquareCertificate (supported_one)
open YMGap.Continuum.QuaternionHaarFiniteProductOrder (environment environment_coordinate)
open YMGap.Continuum.BF4ExactSlabPolynomialActionLocalization (scalarProduct)
open YMGap.Continuum.RGTransport (qpow)
open YMGap.Continuum.QPolyHaarPositiveSubstitution (haar_one)

local infix:50 " ≈ " => Q'.eqv

private theorem mc {a b c d : Q'} (h : a ≈ b) (k : c ≈ d) : a*c ≈ b*d :=
  Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ h) (Q'.mul_eqv_congr_left _ _ _ k)

/-- Literal one-link powers in the supplied ORIGINAL block slots, retaining
the supplied order and repetitions. Moment factorization below needs Nodup. -/
def selectedKernel : List Nat → Nat → RatPoly
  | [], _ => polyOne
  | b::bs, m => polyMul (liftBoundary b (kernelPower m)) (selectedKernel bs m)

private theorem kernel_supported (b m : Nat) :
    SupportedQuaternionBlocks (b+1) (liftBoundary b (kernelPower m)) := by
  simpa only [Nat.add_comm] using lift_supported (kernelPower_supported m) b

/-- No selected coordinate lies outside the declared original carrier. -/
theorem selectedKernel_supported (blocks : Nat) : ∀ (bs : List Nat) (m : Nat),
    (∀ b, b ∈ bs → b < blocks) → SupportedQuaternionBlocks blocks (selectedKernel bs m)
  | [], _, _ => supported_one blocks
  | b::bs, m, hb => by
      apply supported_polyMul
      · intro term ht
        exact Nat.le_trans (kernel_supported b m term ht)
          (Nat.mul_le_mul_left 4 (by have := hb b List.mem_cons_self; omega))
      · exact selectedKernel_supported blocks bs m
          (fun c hc => hb c (List.mem_cons_of_mem b hc))

private theorem kernel_head_local : ∀ m : Nat,
    BlockLocal 1 (fun b => b=0) (kernelPower m)
  | 0 => BlockLocal.one _ _
  | m+1 => (kernel_head_local m).mul
      (((BlockLocal.one 1 (fun b => b=0)).add
        (BlockLocal.coordinate 0 (by decide))).smul half)

private theorem kernel_shift_local : ∀ b m : Nat,
    BlockLocal (b+1) (fun c => c=b) (liftBoundary b (kernelPower m))
  | 0, m => kernel_head_local m
  | b+1, m => by
      have hh := BlockLocal.liftHead (blocks := b+2) (kernel_shift_local b m)
      intro term ht c hc hn
      apply hh term ht c hc
      intro ha
      apply hn
      have hpos := ha.1
      have heq := ha.2
      omega

private theorem kernel_local (blocks b m : Nat) :
    BlockLocal blocks (fun c => c=b) (liftBoundary b (kernelPower m)) := by
  intro term ht c hc hn component hcomponent
  by_cases hsmall : c < b+1
  · exact kernel_shift_local b m term ht c hsmall hn component hcomponent
  · exact exponentAt_of_length_le _ _
      (Nat.le_trans (kernel_supported b m term ht) (by omega))

private theorem selected_local (blocks : Nat) : ∀ bs m,
    BlockLocal blocks (fun b => b ∈ bs) (selectedKernel bs m)
  | [], _ => BlockLocal.one _ _
  | b::bs, m => by
      have hleft : BlockLocal blocks (fun c => c ∈ b::bs)
          (liftBoundary b (kernelPower m)) := by
        intro term ht c hc hn
        exact kernel_local blocks b m term ht c hc
          (fun he => hn (List.mem_cons.mpr (Or.inl he)))
      have hright : BlockLocal blocks (fun c => c ∈ b::bs) (selectedKernel bs m) := by
        intro term ht c hc hn
        exact selected_local blocks bs m term ht c hc
          (fun hm => hn (List.mem_cons_of_mem b hm))
      exact hleft.mul hright

private theorem mono_shift (rho : Nat → Q') (s : Nat) : ∀ (mon : List Nat) (i : Nat),
    evalMonoFrom rho (s+i) mon = evalMonoFrom (fun j => rho (s+j)) i mon
  | [], _ => rfl
  | _::mon, i => by
      simp only [evalMonoFrom]
      rw [show s+i+1=s+(i+1) from Nat.add_assoc _ _ _, mono_shift rho s mon (i+1)]

private theorem mono_lift (rho : Nat → Q') (mon : List Nat) :
    evalMono rho (0::0::0::0::mon) ≈ evalMono (fun i => rho (4+i)) mon := by
  have ht : evalMonoFrom rho 4 mon = evalMono (fun i => rho (4+i)) mon := by
    simpa only [evalMono, Nat.add_zero] using mono_shift rho 4 mon 0
  change 1*(1*(1*(1*evalMonoFrom rho 4 mon))) ≈ _
  rw [ht]
  exact Q'.eqv_trans _ _ _ (Q'.one_mul_eqv _)
    (Q'.eqv_trans _ _ _ (Q'.one_mul_eqv _)
      (Q'.eqv_trans _ _ _ (Q'.one_mul_eqv _) (Q'.one_mul_eqv _)))

private theorem eval_liftHead (rho : Nat → Q') : ∀ p : RatPoly,
    evalRatPoly rho (liftHead p) ≈ evalRatPoly (fun i => rho (4+i)) p
  | [] => Q'.eqv_refl _
  | term::p => Q'.add_eqv_congr'
      (Q'.mul_eqv_congr_left _ _ _ (mono_lift rho term.1)) (eval_liftHead rho p)

private theorem eval_liftBoundary (rho : Nat → Q') : ∀ (blocks : Nat) (p : RatPoly),
    evalRatPoly rho (liftBoundary blocks p) ≈ evalRatPoly (fun i => rho (4*blocks+i)) p
  | 0, p => by
      simp only [liftBoundary, Nat.mul_zero, Nat.zero_add]
      exact Q'.eqv_refl _
  | blocks+1, p => by
      refine Q'.eqv_trans _ _ _ (eval_liftHead rho (liftBoundary blocks p)) ?_
      have he := eval_liftBoundary (fun i => rho (4+i)) blocks p
      have henv : (fun i => rho (4+(4*blocks+i))) = (fun i => rho (4*(blocks+1)+i)) := by
        funext i
        congr 1
        omega
      rw [henv] at he
      exact he

private theorem kernelBase_eval (rho : Nat → Q') :
    evalRatPoly rho kernelBase ≈ half*(1+rho 0) := by
  change evalRatPoly rho (polySmul half (polyAdd polyOne (polyVar 0))) ≈ _
  exact Q'.eqv_trans _ _ _ (evalRatPoly_smul rho _ _)
    (Q'.mul_eqv_congr_left _ _ _ (Q'.eqv_trans _ _ _ (evalRatPoly_add rho _ _)
      (Q'.add_eqv_congr' (evalRatPoly_one rho) (evalRatPoly_var rho 0))))

private theorem kernelPower_eval (rho : Nat → Q') : ∀ m,
    evalRatPoly rho (kernelPower m) ≈ qpow (half*(1+rho 0)) m
  | 0 => evalRatPoly_one rho
  | m+1 => Q'.eqv_trans _ _ _ (evalRatPoly_mul rho _ _)
      (mc (kernelPower_eval rho m) (kernelBase_eval rho))

private theorem shifted_kernel_eval (qs : Nat → UnitNorm) (b m : Nat) :
    evalRatPoly (environment qs) (liftBoundary b (kernelPower m)) ≈ qpow (base (qs b)) m := by
  refine Q'.eqv_trans _ _ _ (eval_liftBoundary (environment qs) b _) ?_
  have he := kernelPower_eval (fun i => environment qs (4*b+i)) m
  have hs : half*(1+environment qs (4*b+0)) = base (qs b) := by
    have hc : environment qs (4*b+0) = (qs b).val.r :=
      environment_coordinate qs b (0 : Fin 4)
    rw [hc]
    rfl
  rw [hs] at he
  exact he

/-- Literal evaluation pin for the original selected slots. No distinctness
or in-carrier guard is needed for this finite polynomial identity. -/
theorem selectedKernel_eval : ∀ (bs : List Nat) (m : Nat) (qs : Nat → UnitNorm),
    evalRatPoly (environment qs) (selectedKernel bs m) ≈
      scalarProduct (fun b => qpow (base (qs b)) m) bs
  | [], _, qs => evalRatPoly_one (environment qs)
  | b::bs, m, qs => Q'.eqv_trans _ _ _ (evalRatPoly_mul _ _ _)
      (mc (shifted_kernel_eval qs b m) (selectedKernel_eval bs m qs))

/-- Exact Haar product of one-link moments. Distinctness is required only
here: repeated block powers cannot be integrated as independent factors. -/
theorem selectedKernel_haar (blocks : Nat) : ∀ (bs : List Nat) (m : Nat),
    (∀ b, b ∈ bs → b < blocks) → bs.Nodup →
    quaternionHaar blocks (selectedKernel bs m) ≈ (kernelMoment m)^bs.length
  | [], _, _, _ => haar_one blocks
  | b::bs, m, hb, hn => by
      have hn' := List.nodup_cons.mp hn
      have ht (c : Nat) (hc : c ∈ bs) : c < blocks := hb c (List.mem_cons_of_mem b hc)
      have hk : SupportedQuaternionBlocks blocks (liftBoundary b (kernelPower m)) :=
        fun term hterm => Nat.le_trans (kernel_supported b m term hterm)
          (Nat.mul_le_mul_left 4 (by have := hb b List.mem_cons_self; omega))
      have hd : BlockDisjoint blocks (liftBoundary b (kernelPower m)) (selectedKernel bs m) := by
        intro s hs t ht' c hc
        by_cases he : c=b
        · right
          exact selected_local blocks bs m t ht' c hc (fun hm => hn'.1 (he ▸ hm))
        · left
          exact kernel_local blocks b m s hs c hc he
      have hsingle : quaternionHaar blocks (liftBoundary b (kernelPower m)) ≈ kernelMoment m :=
        Q'.eqv_trans _ _ _
          (quaternionHaar_extend_supported_endpoint (by have := hb b List.mem_cons_self; omega)
            _ (kernel_supported b m))
          (by simpa only [Nat.add_comm] using haar_liftBoundary b 1 (kernelPower m))
      exact Q'.eqv_trans _ _ _ (haar_product hk (selectedKernel_supported blocks bs m ht) hd)
        (mc hsingle (selectedKernel_haar blocks bs m ht hn'.2))

private theorem mono_eval_zero (rho : Nat → Q') : ∀ (mon : List Nat) (i : Nat),
    (∀ j, exponentAt mon j = 0) → evalMonoFrom rho i mon ≈ 1
  | [], _, _ => Q'.eqv_refl _
  | e::mon, i, hz => by
      have he : e=0 := hz 0
      subst e
      exact Q'.eqv_trans _ _ _ (Q'.one_mul_eqv _)
        (mono_eval_zero rho mon (i+1) (fun j => hz (j+1)))

private theorem mono_haar_zero (blocks : Nat) (mon : List Nat)
    (hz : ∀ j, exponentAt mon j = 0) : quaternionHaarMono blocks mon ≈ 1 := by
  have ht : allZero (mon.drop (4*blocks)) = true :=
    (allZero_iff _).mpr (fun j => by rw [exponentAt_drop]; exact hz _)
  have hp : quaternionHaarPrefix blocks mon = quaternionHaarPrefix blocks [] :=
    prefix_congr blocks mon [] (fun j _ => by rw [hz j]; rfl)
  have he : quaternionHaarMono blocks mon = quaternionHaarMono blocks [] := by
    simp only [quaternionHaarMono, ht, if_true, List.drop_nil]
    exact hp
  rw [he]
  exact quaternionHaarMono_one blocks

private theorem constant_eval_haar (blocks : Nat) (rho : Nat → Q') : ∀ p : RatPoly,
    (∀ term, term ∈ p → ∀ j, exponentAt term.1 j = 0) →
    evalRatPoly rho p ≈ quaternionHaar blocks p
  | [], _ => Q'.eqv_refl _
  | term::p, hz => Q'.add_eqv_congr'
      (Q'.mul_eqv_congr_left _ _ _
        (Q'.eqv_trans _ _ _ (mono_eval_zero rho term.1 0 (hz term List.mem_cons_self))
          (Q'.eqv_symm (mono_haar_zero blocks term.1 (hz term List.mem_cons_self)))))
      (constant_eval_haar blocks rho p (fun t ht => hz t (List.mem_cons_of_mem term ht)))

/-- The ORIGINAL selected-block projection is constant at every remaining
assignment, including zero blocks, an empty schedule and exponent zero. -/
theorem selectedKernel_project_eval (blocks : Nat) (bs : List Nat) (m : Nat)
    (hbs : ∀ b, b ∈ bs → b < blocks) (hn : bs.Nodup) (qs : Nat → UnitNorm) :
    evalRatPoly (environment qs) (familyProject bs (selectedKernel bs m)) ≈
      (kernelMoment m)^bs.length := by
  have hs := familyProject_supported bs (selectedKernel_supported blocks bs m hbs)
  have hl := integrateBlocks_local bs (selected_local blocks bs m)
  have hz : ∀ term, term ∈ familyProject bs (selectedKernel bs m) →
      ∀ j, exponentAt term.1 j = 0 := by
    intro term ht j
    by_cases hj : j < 4*blocks
    · have hb : j/4 < blocks := by omega
      have he : 4*(j/4)+j%4=j := by omega
      have h := hl term ht (j/4) hb (fun ha => ha.2 ha.1)
        (j%4) (Nat.mod_lt _ (by decide : 0<4))
      simpa only [he] using h
    · exact exponentAt_of_length_le _ _ (Nat.le_trans (hs term ht) (by omega))
  exact Q'.eqv_trans _ _ _ (constant_eval_haar blocks (environment qs) _ hz)
    (Q'.eqv_trans _ _ _ (familyProject_mean blocks bs hbs (selectedKernel bs m))
      (selectedKernel_haar blocks bs m hbs hn))

private theorem pow_mono {a b : Q'} (ha : (0 : Q') ≤ a) (hab : a ≤ b) :
    ∀ k : Nat, a^k ≤ b^k
  | 0 => Q'.le_refl' _
  | k+1 => Q'.mul_le_mul_of_nonneg hab (pow_mono ha hab k)
      (Q'.le_trans' _ _ _ ha hab) (Q'.pow_nonneg a ha k)

private theorem pow_positive (a : Q') (ha : (0 : Q') < a) : ∀ k : Nat, (0 : Q') < a^k
  | 0 => by change (0 : Q') < 1; decide
  | k+1 => Q'.mul_pos ha (pow_positive a ha k)

/-- Computed boundary-independent floor for the actual selected marginal. -/
theorem selectedKernel_project_lower (blocks : Nat) (bs : List Nat) (m : Nat)
    (hbs : ∀ b, b ∈ bs → b < blocks) (hn : bs.Nodup) (qs : Nat → UnitNorm) :
    (localizationFloor m)^bs.length ≤
      evalRatPoly (environment qs) (familyProject bs (selectedKernel bs m)) :=
  Q'.le_trans' _ _ _
    (pow_mono (Q'.le_of_lt (localizationFloor_positive m))
      (localizationFloor_le_kernelMoment m) bs.length)
    (Q'.ge_of_eqv (selectedKernel_project_eval blocks bs m hbs hn qs))

/-- The computed selected localization mass is strictly positive, without
requiring a nonempty schedule or a positive exponent. -/
theorem selectedKernel_project_positive (blocks : Nat) (bs : List Nat) (m : Nat)
    (hbs : ∀ b, b ∈ bs → b < blocks) (hn : bs.Nodup) (qs : Nat → UnitNorm) :
    (0 : Q') < evalRatPoly (environment qs) (familyProject bs (selectedKernel bs m)) :=
  HeatKernelRGStep.lt_of_lt_of_le
    (pow_positive _ (localizationFloor_positive m) bs.length)
    (selectedKernel_project_lower blocks bs m hbs hn qs)

end YMGap.Continuum.QuaternionHaarSelectedKernelLocalization

#print axioms YMGap.Continuum.QuaternionHaarSelectedKernelLocalization.selectedKernel
#print axioms YMGap.Continuum.QuaternionHaarSelectedKernelLocalization.selectedKernel_supported
#print axioms YMGap.Continuum.QuaternionHaarSelectedKernelLocalization.selectedKernel_eval
#print axioms YMGap.Continuum.QuaternionHaarSelectedKernelLocalization.selectedKernel_haar
#print axioms YMGap.Continuum.QuaternionHaarSelectedKernelLocalization.selectedKernel_project_eval
#print axioms YMGap.Continuum.QuaternionHaarSelectedKernelLocalization.selectedKernel_project_lower
#print axioms YMGap.Continuum.QuaternionHaarSelectedKernelLocalization.selectedKernel_project_positive
