/-
# Exact SU(2) fusion support lost by the BF4 inward mate

At a link on the boundary of the selected cube, the inward mate changes the
two incident cube-face labels together.  If both labels are positive, lowering
both by one preserves their complete Clebsch--Gordan ladder except for the
single stretched channel `channel = left + right`.  If an even label is zero,
the compensating move `0 -> 1` preserves every old channel.

Thus a source fusion can fail after the even inward mate exactly when both
source labels are positive and the resolved strand uses the stretched
channel.  For an odd pair, positivity is automatic and the same statement has
no zero exception.  This identifies the precise local debt that a global
non-abelian strand rerouting must pay; it does not construct that rerouting or
assert a multiplicity, transition, Poincare, spectral-gap, or continuum bound.

No `Classical`, choice, `native_decide`, `sorry`, custom axiom, noncomputable
declaration, or trusted external computation is used.
-/

import YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateHeatBound
import YMGap.Continuum.FusionBratteli
import YMGap.Continuum.FusionQuotientCollapse
import YMGap.Continuum.Z4FusionPathZeroInsertion

namespace YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateFusionSupport

open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateHeatBound
open YMGap.Continuum.BondMovingStep
open YMGap.Continuum.FusionBratteli
open YMGap.Continuum.FusionQuotientCollapse
open YMGap.Continuum.Z4ExplicitValenceFusionMultiplicity
open YMGap.Continuum.Z4FiniteBoxFusionCompleteCutoff
open YMGap.Continuum.Z4FusionPathZeroInsertion
open YMGap.Continuum.Z4ValenceFusionCutoffIndependence

/-! ## 1. Positive pairs lose only their stretched channel -/

/-- Lowering two positive SU(2) labels by one preserves every supported
channel except possibly the unique stretched channel. -/
theorem fusionOK_positivePred_or_stretched
    (left right channel : Nat)
    (hleft : 0 < left) (hright : 0 < right)
    (hsource : fusionOK left right channel = true) :
    fusionOK (left - 1) (right - 1) channel = true ∨
      channel = left + right := by
  obtain ⟨depth, hdepthLeft, hdepthRight, hsum⟩ :=
    (fusionOK_iff_ladder left right channel).mp hsource
  by_cases hdepthZero : depth = 0
  · apply Or.inr
    omega
  · apply Or.inl
    apply (fusionOK_iff_ladder
      (left - 1) (right - 1) channel).mpr
    exact ⟨depth - 1, by omega, by omega, by omega⟩

/-- The stretched source channel is absent after lowering two positive labels
by one. -/
theorem fusionOK_positivePred_stretched_eq_false
    (left right : Nat) (hleft : 0 < left) (hright : 0 < right) :
    fusionOK (left - 1) (right - 1) (left + right) = false := by
  rw [fusionOK_eq_false_iff]
  rintro ⟨_, hupper, _⟩
  omega

/-- On a supported positive pair, failure after simultaneous predecessor
lowering is equivalent to use of the stretched source channel. -/
theorem fusionOK_positivePred_eq_false_iff_stretched
    (left right channel : Nat)
    (hleft : 0 < left) (hright : 0 < right)
    (hsource : fusionOK left right channel = true) :
    fusionOK (left - 1) (right - 1) channel = false ↔
      channel = left + right := by
  constructor
  · intro htarget
    rcases fusionOK_positivePred_or_stretched
        left right channel hleft hright hsource with hpreserved | hstretched
    · rw [hpreserved] at htarget
      contradiction
    · exact hstretched
  · intro hstretched
    subst channel
    exact fusionOK_positivePred_stretched_eq_false
      left right hleft hright

/-! ## 2. Exact even- and odd-mate classifications -/

/-- Every source channel survives the zero-compensating inward mate except
possibly a stretched channel between two positive labels.  In particular,
this applies to the same-parity even pairs in the physical BF4 move. -/
theorem fusionOK_evenInwardMate_or_positive_stretched
    (left right channel : Nat)
    (hsource : fusionOK left right channel = true) :
    fusionOK (evenInwardMateLabel left)
        (evenInwardMateLabel right) channel = true ∨
      (0 < left ∧ 0 < right ∧ channel = left + right) := by
  obtain ⟨depth, hdepthLeft, hdepthRight, hsum⟩ :=
    (fusionOK_iff_ladder left right channel).mp hsource
  by_cases hleftZero : left = 0
  · subst left
    by_cases hrightZero : right = 0
    · subst right
      apply Or.inl
      change fusionOK 1 1 channel = true
      apply (fusionOK_iff_ladder 1 1 channel).mpr
      exact ⟨1, by omega, by omega, by omega⟩
    · apply Or.inl
      have hrightPos : 0 < right := Nat.pos_of_ne_zero hrightZero
      unfold evenInwardMateLabel
      rw [if_pos rfl, if_neg hrightZero]
      apply (fusionOK_iff_ladder 1 (right - 1) channel).mpr
      exact ⟨0, by omega, by omega, by omega⟩
  · have hleftPos : 0 < left := Nat.pos_of_ne_zero hleftZero
    by_cases hrightZero : right = 0
    · subst right
      apply Or.inl
      unfold evenInwardMateLabel
      rw [if_neg hleftZero, if_pos rfl]
      apply (fusionOK_iff_ladder (left - 1) 1 channel).mpr
      exact ⟨0, by omega, by omega, by omega⟩
    · have hrightPos : 0 < right := Nat.pos_of_ne_zero hrightZero
      unfold evenInwardMateLabel
      rw [if_neg hleftZero, if_neg hrightZero]
      rcases fusionOK_positivePred_or_stretched
          left right channel hleftPos hrightPos hsource with
        hpreserved | hstretched
      · exact Or.inl hpreserved
      · exact Or.inr ⟨hleftPos, hrightPos, hstretched⟩

/-- Exact local debt of the even inward mate: on a supported even pair, the
target fusion fails iff both source labels are positive and their channel is
stretched. -/
theorem fusionOK_evenInwardMate_eq_false_iff
    (left right channel : Nat)
    (hsource : fusionOK left right channel = true) :
    fusionOK (evenInwardMateLabel left)
        (evenInwardMateLabel right) channel = false ↔
      (0 < left ∧ 0 < right ∧ channel = left + right) := by
  constructor
  · intro htarget
    rcases fusionOK_evenInwardMate_or_positive_stretched
        left right channel hsource with
      hpreserved | hdebt
    · rw [hpreserved] at htarget
      contradiction
    · exact hdebt
  · rintro ⟨hleft, hright, hstretched⟩
    unfold evenInwardMateLabel
    rw [if_neg (Nat.ne_of_gt hleft), if_neg (Nat.ne_of_gt hright)]
    subst channel
    exact fusionOK_positivePred_stretched_eq_false
      left right hleft hright

/-- Odd labels are automatically positive, so the only channel lost under
their inward mate is the stretched channel. -/
theorem fusionOK_oddInwardMate_eq_false_iff
    (left right channel : Nat)
    (hleftOdd : left % 2 = 1) (hrightOdd : right % 2 = 1)
    (hsource : fusionOK left right channel = true) :
    fusionOK (oddInwardMateLabel left)
        (oddInwardMateLabel right) channel = false ↔
      channel = left + right := by
  have hleft : 0 < left := by omega
  have hright : 0 < right := by omega
  unfold oddInwardMateLabel
  exact fusionOK_positivePred_eq_false_iff_stretched
    left right channel hleft hright hsource

/-! ## 3. One resolved-link multiplicity has one explicit debt channel -/

private theorem natListSum_map_le_add
    {Item : Type} (source target debt : Item → Nat) :
    ∀ items : List Item,
      (∀ item, item ∈ items →
        source item ≤ target item + debt item) →
      natListSum (items.map source) ≤
        natListSum (items.map target) +
          natListSum (items.map debt)
  | [], _ => Nat.le_refl 0
  | item :: items, hpointwise => by
      simp only [List.map_cons, natListSum]
      have hhead := hpointwise item List.mem_cons_self
      have htail := natListSum_map_le_add source target debt items
        (fun next hnext =>
          hpointwise next (List.mem_cons_of_mem item hnext))
      omega

private theorem natListSum_range_single
    (cutoff chosen value : Nat) :
    natListSum
        ((List.range (cutoff + 1)).map fun index =>
          if index = chosen then value else 0) =
      if chosen ≤ cutoff then value else 0 := by
  induction cutoff with
  | zero =>
      change (if 0 = chosen then value else 0) =
        if chosen ≤ 0 then value else 0
      by_cases hchosen : chosen = 0
      · subst chosen
        rfl
      · have hpositive : 0 < chosen := Nat.pos_of_ne_zero hchosen
        rw [if_neg (by omega), if_neg (by omega)]
  | succ cutoff ih =>
      rw [List.range_succ, List.map_append, natListSum_append]
      simp only [List.map_singleton, natListSum, Nat.add_zero, ih]
      by_cases hbelow : chosen ≤ cutoff
      · rw [if_pos hbelow, if_neg (by omega), if_pos (by omega)]
        omega
      · by_cases htop : chosen = cutoff + 1
        · subst chosen
          rw [if_neg (by omega), if_pos rfl, if_pos (by omega)]
          exact Nat.zero_add value
        · rw [if_neg hbelow, if_neg (by omega), if_neg (by omega)]

/-- At the level of the actual left-associated SU(2) fusion-path count,
changing the first pair by the zero-compensating inward mate costs at most
one explicit continuation: the source's stretched channel.  All other source
paths inject into the mate resolver with their channel unchanged. -/
theorem fusionPathMultiplicity_evenInwardMate_le_add_stretched
    (cutoff left right : Nat) (rest : List Nat)
    (hstretchedCutoff : left + right ≤ cutoff) :
    fusionPathMultiplicity cutoff (left :: right :: rest) ≤
      fusionPathMultiplicity cutoff
          (evenInwardMateLabel left ::
            evenInwardMateLabel right :: rest) +
        fusionPathMultiplicity cutoff ((left + right) :: rest) := by
  rw [fusionPathMultiplicity_cons_cons,
    fusionPathMultiplicity_cons_cons]
  let continuation := fun channel =>
    fusionPathMultiplicity cutoff (channel :: rest)
  let sourceTerm := fun channel =>
    if fusionOK left right channel then continuation channel else 0
  let targetTerm := fun channel =>
    if fusionOK (evenInwardMateLabel left)
        (evenInwardMateLabel right) channel then
      continuation channel
    else 0
  let debtTerm := fun channel =>
    if channel = left + right then continuation channel else 0
  change natListSum ((List.range (cutoff + 1)).map sourceTerm) ≤
    natListSum ((List.range (cutoff + 1)).map targetTerm) +
      continuation (left + right)
  have hpointwise : ∀ channel,
      channel ∈ List.range (cutoff + 1) →
      sourceTerm channel ≤ targetTerm channel + debtTerm channel := by
    intro channel _hchannel
    unfold sourceTerm targetTerm debtTerm
    cases hsource : fusionOK left right channel with
    | false => simp only [Bool.false_eq_true, if_false, Nat.zero_le]
    | true =>
        simp only [if_true]
        rcases fusionOK_evenInwardMate_or_positive_stretched
            left right channel hsource with hpreserved | hstretched
        · rw [if_pos hpreserved]
          exact Nat.le_add_right _ _
        · rw [if_pos hstretched.2.2]
          exact Nat.le_add_left _ _
  have hsum := natListSum_map_le_add
    sourceTerm targetTerm debtTerm (List.range (cutoff + 1)) hpointwise
  have hdebt :
      natListSum ((List.range (cutoff + 1)).map debtTerm) =
        continuation (left + right) := by
    unfold debtTerm
    calc
      natListSum
          ((List.range (cutoff + 1)).map fun channel =>
            if channel = left + right then continuation channel else 0) =
          natListSum
            ((List.range (cutoff + 1)).map fun channel =>
              if channel = left + right then
                continuation (left + right)
              else 0) := by
        apply natListSum_map_congr
        intro channel _hchannel
        by_cases hchannel : channel = left + right
        · subst channel
          rfl
        · rw [if_neg hchannel, if_neg hchannel]
      _ = continuation (left + right) := by
        rw [natListSum_range_single cutoff (left + right)
          (continuation (left + right)), if_pos hstretchedCutoff]
  rw [hdebt] at hsum
  exact hsum

/-- On an odd physical pair the zero-compensating mate is the ordinary
predecessor mate, so the same single stretched-continuation bound applies. -/
theorem fusionPathMultiplicity_oddInwardMate_le_add_stretched
    (cutoff left right : Nat) (rest : List Nat)
    (hleftOdd : left % 2 = 1) (hrightOdd : right % 2 = 1)
    (hstretchedCutoff : left + right ≤ cutoff) :
    fusionPathMultiplicity cutoff (left :: right :: rest) ≤
      fusionPathMultiplicity cutoff
          (oddInwardMateLabel left :: oddInwardMateLabel right :: rest) +
        fusionPathMultiplicity cutoff ((left + right) :: rest) := by
  have hleft : 0 < left := by omega
  have hright : 0 < right := by omega
  have hleftMate :
      evenInwardMateLabel left = oddInwardMateLabel left := by
    unfold evenInwardMateLabel oddInwardMateLabel
    rw [if_neg (Nat.ne_of_gt hleft)]
  have hrightMate :
      evenInwardMateLabel right = oddInwardMateLabel right := by
    unfold evenInwardMateLabel oddInwardMateLabel
    rw [if_neg (Nat.ne_of_gt hright)]
  rw [← hleftMate, ← hrightMate]
  exact fusionPathMultiplicity_evenInwardMate_le_add_stretched
    cutoff left right rest hstretchedCutoff

private theorem evenInwardMateLabel_le
    {K spin : Nat} (hK : 1 ≤ K) (hspin : spin ≤ K) :
    evenInwardMateLabel spin ≤ K := by
  unfold evenInwardMateLabel
  by_cases hzero : spin = 0
  · rw [if_pos hzero]
    exact hK
  · rw [if_neg hzero]
    omega

/-- Production-level specialization for an actual valence-at-most-six link.
The physical labels are bounded by `K`, while the one stretched debt label is
bounded by the production auxiliary cutoff `6*K`.  Hence the explicit local
intertwiner multiplicity is at most the inward-mate multiplicity plus the
single stretched-continuation multiplicity. -/
theorem explicitValenceMultiplicity_physical_inwardMate_le_add_stretched
    (K left right : Nat) (rest : List Nat)
    (hK : 1 ≤ K)
    (hlength : (left :: right :: rest).length ≤ 6)
    (hbounded : SpinsBounded K (left :: right :: rest)) :
    explicitValenceMultiplicity (linkAuxiliaryCutoff K)
        (left :: right :: rest).length
        (externalSpinsOfList (left :: right :: rest)) ≤
      explicitValenceMultiplicity (linkAuxiliaryCutoff K)
          (evenInwardMateLabel left ::
            evenInwardMateLabel right :: rest).length
          (externalSpinsOfList
            (evenInwardMateLabel left ::
              evenInwardMateLabel right :: rest)) +
        explicitValenceMultiplicity (linkAuxiliaryCutoff K)
          ((left + right) :: rest).length
          (externalSpinsOfList ((left + right) :: rest)) := by
  have hleftK : left ≤ K := hbounded left (by simp)
  have hrightK : right ≤ K := hbounded right (by simp)
  have hrestK : SpinsBounded K rest := by
    intro spin hspin
    exact hbounded spin (by simp [hspin])
  have hKaux : K ≤ linkAuxiliaryCutoff K :=
    externalCutoff_le_linkAuxiliaryCutoff K
  have holdAux :
      SpinsBounded (linkAuxiliaryCutoff K) (left :: right :: rest) := by
    intro spin hspin
    exact Nat.le_trans (hbounded spin hspin) hKaux
  have hmateK : SpinsBounded K
      (evenInwardMateLabel left ::
        evenInwardMateLabel right :: rest) := by
    intro spin hspin
    rcases List.mem_cons.mp hspin with hspin | hspin
    · subst spin
      exact evenInwardMateLabel_le hK hleftK
    · rcases List.mem_cons.mp hspin with hspin | hspin
      · subst spin
        exact evenInwardMateLabel_le hK hrightK
      · exact hrestK spin hspin
  have hmateAux : SpinsBounded (linkAuxiliaryCutoff K)
      (evenInwardMateLabel left ::
        evenInwardMateLabel right :: rest) := by
    intro spin hspin
    exact Nat.le_trans (hmateK spin hspin) hKaux
  have hstretchedAux : left + right ≤ linkAuxiliaryCutoff K := by
    unfold linkAuxiliaryCutoff linkIncidenceBound
    omega
  have hdebtAux : SpinsBounded (linkAuxiliaryCutoff K)
      ((left + right) :: rest) := by
    intro spin hspin
    rcases List.mem_cons.mp hspin with hspin | hspin
    · subst spin
      exact hstretchedAux
    · exact Nat.le_trans (hrestK spin hspin) hKaux
  have hmateLength :
      (evenInwardMateLabel left ::
        evenInwardMateLabel right :: rest).length ≤ 6 := by
    simpa only [List.length_cons] using hlength
  have hdebtLength : ((left + right) :: rest).length ≤ 6 := by
    simp only [List.length_cons] at hlength ⊢
    omega
  rw [← fusionPathMultiplicity_eq_explicit_of_length_le_six
        (left :: right :: rest) hlength holdAux,
    ← fusionPathMultiplicity_eq_explicit_of_length_le_six
        (evenInwardMateLabel left ::
          evenInwardMateLabel right :: rest) hmateLength hmateAux,
    ← fusionPathMultiplicity_eq_explicit_of_length_le_six
        ((left + right) :: rest) hdebtLength hdebtAux]
  exact fusionPathMultiplicity_evenInwardMate_le_add_stretched
    (linkAuxiliaryCutoff K) left right rest hstretchedAux

end YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateFusionSupport

/-! ## Axiom-dependency gates -/

#print axioms
  YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateFusionSupport.fusionOK_positivePred_or_stretched
#print axioms
  YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateFusionSupport.fusionOK_positivePred_stretched_eq_false
#print axioms
  YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateFusionSupport.fusionOK_positivePred_eq_false_iff_stretched
#print axioms
  YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateFusionSupport.fusionOK_evenInwardMate_or_positive_stretched
#print axioms
  YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateFusionSupport.fusionOK_evenInwardMate_eq_false_iff
#print axioms
  YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateFusionSupport.fusionOK_oddInwardMate_eq_false_iff
#print axioms
  YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateFusionSupport.fusionPathMultiplicity_evenInwardMate_le_add_stretched
#print axioms
  YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateFusionSupport.fusionPathMultiplicity_oddInwardMate_le_add_stretched
#print axioms
  YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateFusionSupport.explicitValenceMultiplicity_physical_inwardMate_le_add_stretched
