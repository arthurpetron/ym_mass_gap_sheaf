/-
# Compile an explicit plaquette path into one connected pair carrier

An adjacency path between two literal plaquettes is enough data to build the
single connected `ProbeCarrier` required by guarded covariance insertion.
The path vertices are deduplicated constructively, retain both endpoints and
form a genuine rooted connected animal.  Its support has at most
`pathLen + 1` faces, so later margin estimates pay the actual supplied
corridor length rather than a box-volume surrogate.

This module does not construct a path for any particular observables and does
not prove an insertion, telescope, summability, continuum or mass-gap bound.
-/

import YMGap.Continuum.BF4ExactSlabProbeCarrierAnimal
import YMGap.Continuum.SepLatticeZ4Linf

namespace YMGap.Continuum.BF4ExactSlabPlaquettePairPathCarrier

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.AdjSpanningBuild (adjacentSymm)
open YMGap.Continuum.BF4ExactSlabFaceLinkLocality
open YMGap.Continuum.BF4ExactSlabProbeCarrierAnimal
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.FiniteRootedAnimalTourCode
open YMGap.Continuum.PinnedCluster
open YMGap.Continuum.PolymerModel
open YMGap.Continuum.SepLatticeZ4Linf
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier

private instance z4SepLinfPlaquetteBEq :
    BEq z4SepLinf.toLattice.Plaquette where
  beq left right :=
    @decide (left = right) (z4Chain.decEq left right)

private instance z4SepLinfPlaquetteLawfulBEq :
    LawfulBEq z4SepLinf.toLattice.Plaquette where
  eq_of_beq {left right} h :=
    @of_decide_eq_true (left = right) (z4Chain.decEq left right) h
  rfl {plaquette} :=
    @of_decide_eq_self_eq_true z4SepLinf.toLattice.Plaquette
      z4Chain.decEq plaquette

private def chainInMono {small large : List Z4Plaq}
    (hsubset : ∀ plaquette, plaquette ∈ small → plaquette ∈ large) :
    {first last : Z4Plaq} →
      ChainIn z4Lattice small first last →
      ChainIn z4Lattice large first last
  | _, _, .refl plaquette => .refl plaquette
  | _, _, .step adjacent hnext rest =>
      .step adjacent (hsubset _ hnext) (chainInMono hsubset rest)

private def chainInTrans {support : List Z4Plaq} :
    {first middle last : Z4Plaq} →
      ChainIn z4Lattice support first middle →
      ChainIn z4Lattice support middle last →
      ChainIn z4Lattice support first last
  | _, _, _, .refl _, right => right
  | _, _, _, .step adjacent hnext rest, right =>
      .step adjacent hnext (chainInTrans rest right)

private def connectedIn_cons_of_tail_bridge
    {head parent : Z4Plaq} {tail : List Z4Plaq}
    (htail : connectedIn (L := z4Lattice) tail)
    (hparent : parent ∈ tail)
    (hadjacent : z4Lattice.Adjacent head parent) :
    connectedIn (L := z4Lattice) (head :: tail) := by
  intro first last hfirst hlast
  cases z4Chain.decEq first head with
  | isTrue hfirstHead =>
      subst first
      cases z4Chain.decEq last head with
      | isTrue hlastHead =>
          subst last
          exact @ChainIn.refl z4Lattice (head :: tail) head
      | isFalse hlastHead =>
          have hlastTail : last ∈ tail :=
            (List.mem_cons.mp hlast).resolve_left hlastHead
          exact .step hadjacent (List.mem_cons_of_mem head hparent)
            (chainInMono
              (fun plaquette hplaquette =>
                List.mem_cons_of_mem head hplaquette)
              (htail parent last hparent hlastTail))
  | isFalse hfirstHead =>
      have hfirstTail : first ∈ tail :=
        (List.mem_cons.mp hfirst).resolve_left hfirstHead
      cases z4Chain.decEq last head with
      | isTrue hlastHead =>
          subst last
          exact chainInTrans
            (chainInMono
              (fun plaquette hplaquette =>
                List.mem_cons_of_mem head hplaquette)
              (htail first parent hfirstTail hparent))
            (.step (adjacentSymm hadjacent) List.mem_cons_self
              (@ChainIn.refl z4Lattice (head :: tail) head))
      | isFalse hlastHead =>
          have hlastTail : last ∈ tail :=
            (List.mem_cons.mp hlast).resolve_left hlastHead
          exact chainInMono
            (fun plaquette hplaquette =>
              List.mem_cons_of_mem head hplaquette)
            (htail first last hfirstTail hlastTail)

private theorem filteredEraseDupsNodupLocal {A : Type}
    [BEq A] [LawfulBEq A] (items : List A) :
    ∀ predicate : A → Bool, (items.filter predicate).eraseDups.Nodup := by
  induction items with
  | nil =>
      intro _
      exact List.nodup_nil
  | cons head tail ih =>
      intro predicate
      rw [List.filter_cons]
      split
      · rw [List.eraseDups_cons, List.filter_filter]
        refine List.nodup_cons.mpr ⟨?_, ih _⟩
        intro hmem
        have hfiltered := List.mem_eraseDups.mp hmem
        have hfalse := (List.mem_filter.mp hfiltered).2
        have hself : (head == head) = true := BEq.rfl
        rw [hself] at hfalse
        contradiction
      · exact ih _

private theorem filterTrueLocal {A : Type} :
    ∀ items : List A, items.filter (fun _ => true) = items
  | [] => rfl
  | head :: tail => congrArg (List.cons head) (filterTrueLocal tail)

private theorem eraseDupsNodupLocal {A : Type}
    [BEq A] [LawfulBEq A] (items : List A) : items.eraseDups.Nodup := by
  have h := filteredEraseDupsNodupLocal items (fun _ => true)
  rw [filterTrueLocal] at h
  exact h

private theorem eraseDupsLengthLeLocal {A : Type}
    [BEq A] (items : List A) :
    items.eraseDups.length ≤ items.length := by
  cases items with
  | nil => simp
  | cons head tail =>
      rw [List.eraseDups_cons]
      simp only [List.length_cons]
      have hfilter := List.length_filter_le
        (fun item : A => !item == head) tail
      have ih := eraseDupsLengthLeLocal
        (tail.filter fun item => !item == head)
      omega
termination_by items.length
decreasing_by
  simp_wf
  omega

/-- Both endpoints occur in the path's visited list. -/
def endpoints_mem_verts : {left right : Z4Plaq} →
    (path : AdjPath z4SepLinf left right) →
    left ∈ path.verts ∧ right ∈ path.verts
  | _, _, .single _ =>
      ⟨List.mem_cons_self, List.mem_cons_self⟩
  | _, _, .cons _ rest =>
      ⟨List.mem_cons_self,
        List.mem_cons_of_mem _ (endpoints_mem_verts rest).2⟩

/-- The literal vertices of an adjacency path are geometrically connected. -/
def verts_connected : {left right : Z4Plaq} →
    (path : AdjPath z4SepLinf left right) →
    connectedIn (L := z4Lattice) path.verts
  | _, _, .single plaquette => connectedIn_singleton plaquette
  | _, _, .cons adjacent rest =>
      connectedIn_cons_of_tail_bridge (verts_connected rest)
        (endpoints_mem_verts rest).1 adjacent

/-- Deduplicated path vertices used as the finite animal support. -/
def pathSupport {left right : Z4Plaq}
    (path : AdjPath z4SepLinf left right) :
    List z4SepLinf.toLattice.Plaquette :=
  @List.eraseDups z4SepLinf.toLattice.Plaquette
    z4SepLinfPlaquetteBEq path.verts

theorem endpoints_mem_pathSupport {left right : Z4Plaq}
    (path : AdjPath z4SepLinf left right) :
    left ∈ pathSupport path ∧ right ∈ pathSupport path := by
  exact
    ⟨(@List.mem_eraseDups z4SepLinf.toLattice.Plaquette
        z4SepLinfPlaquetteBEq z4SepLinfPlaquetteLawfulBEq
        left path.verts).mpr (endpoints_mem_verts path).1,
      (@List.mem_eraseDups z4SepLinf.toLattice.Plaquette
        z4SepLinfPlaquetteBEq z4SepLinfPlaquetteLawfulBEq
        right path.verts).mpr (endpoints_mem_verts path).2⟩

theorem pathSupport_nodup {left right : Z4Plaq}
    (path : AdjPath z4SepLinf left right) :
    (pathSupport path).Nodup := by
  exact @eraseDupsNodupLocal z4SepLinf.toLattice.Plaquette
    z4SepLinfPlaquetteBEq z4SepLinfPlaquetteLawfulBEq path.verts

def pathSupport_connected {left right : Z4Plaq}
    (path : AdjPath z4SepLinf left right) :
    connectedIn (L := z4Lattice) (pathSupport path) := by
  intro first last hfirst hlast
  change first ∈ (@List.eraseDups z4SepLinf.toLattice.Plaquette
    z4SepLinfPlaquetteBEq path.verts) at hfirst
  change last ∈ (@List.eraseDups z4SepLinf.toLattice.Plaquette
    z4SepLinfPlaquetteBEq path.verts) at hlast
  exact chainInMono
    (fun plaquette hplaquette =>
      (@List.mem_eraseDups z4SepLinf.toLattice.Plaquette
        z4SepLinfPlaquetteBEq z4SepLinfPlaquetteLawfulBEq
        plaquette path.verts).mpr hplaquette)
    (verts_connected path first last
      ((@List.mem_eraseDups z4SepLinf.toLattice.Plaquette
        z4SepLinfPlaquetteBEq z4SepLinfPlaquetteLawfulBEq
        first path.verts).mp hfirst)
      ((@List.mem_eraseDups z4SepLinf.toLattice.Plaquette
        z4SepLinfPlaquetteBEq z4SepLinfPlaquetteLawfulBEq
        last path.verts).mp hlast))

/-- The rooted animal carried by one explicit endpoint-to-endpoint path. -/
def pathAnimal {left right : Z4Plaq}
    (path : AdjPath z4SepLinf left right) : RootedConnectedAnimal z4Chain where
  root := left
  support := pathSupport path
  root_mem := (endpoints_mem_pathSupport path).1
  support_nodup := pathSupport_nodup path
  connected := pathSupport_connected path

/-- Deduplication can only shorten the path's `pathLen + 1` vertex list. -/
theorem pathAnimal_support_length_le {left right : Z4Plaq}
    (path : AdjPath z4SepLinf left right) :
    (pathAnimal path).support.length ≤ path.pathLen + 1 := by
  exact Nat.le_trans
    (@eraseDupsLengthLeLocal z4SepLinf.toLattice.Plaquette
      z4SepLinfPlaquetteBEq path.verts)
    (Nat.le_of_eq (AdjPath.verts_length path))

/-- One connected carrier covering the literal four-link supports of both
endpoint plaquettes. -/
def pairCarrier {left right : Z4Plaq}
    (path : AdjPath z4SepLinf left right) :
    ProbeCarrier (edgesOf left ++ edgesOf right) where
  animal := pathAnimal path
  covers := by
    intro link hlink
    rcases List.mem_append.mp hlink with hleft | hright
    · exact List.mem_flatMap.mpr
        ⟨left, (endpoints_mem_pathSupport path).1, hleft⟩
    · exact List.mem_flatMap.mpr
        ⟨right, (endpoints_mem_pathSupport path).2, hright⟩

theorem pairCarrier_support_length_le {left right : Z4Plaq}
    (path : AdjPath z4SepLinf left right) :
    (pairCarrier path).animal.support.length ≤ path.pathLen + 1 :=
  pathAnimal_support_length_le path

/-- Locality at the left endpoint lifts to the common pair carrier. -/
theorem left_local_on_pair {extent : Nat} {left right : Z4Plaq}
    {polynomial : RatPoly}
    (hlocal : LinkLocal extent (edgesOf left) polynomial) :
    LinkLocal extent (edgesOf left ++ edgesOf right) polynomial :=
  hlocal.mono (fun _ hlink => List.mem_append.mpr (Or.inl hlink))

/-- Locality at the right endpoint lifts to the common pair carrier. -/
theorem right_local_on_pair {extent : Nat} {left right : Z4Plaq}
    {polynomial : RatPoly}
    (hlocal : LinkLocal extent (edgesOf right) polynomial) :
    LinkLocal extent (edgesOf left ++ edgesOf right) polynomial :=
  hlocal.mono (fun _ hlink => List.mem_append.mpr (Or.inr hlink))

end YMGap.Continuum.BF4ExactSlabPlaquettePairPathCarrier

#print axioms YMGap.Continuum.BF4ExactSlabPlaquettePairPathCarrier.endpoints_mem_verts
#print axioms YMGap.Continuum.BF4ExactSlabPlaquettePairPathCarrier.verts_connected
#print axioms YMGap.Continuum.BF4ExactSlabPlaquettePairPathCarrier.pathSupport
#print axioms YMGap.Continuum.BF4ExactSlabPlaquettePairPathCarrier.endpoints_mem_pathSupport
#print axioms YMGap.Continuum.BF4ExactSlabPlaquettePairPathCarrier.pathSupport_nodup
#print axioms YMGap.Continuum.BF4ExactSlabPlaquettePairPathCarrier.pathSupport_connected
#print axioms YMGap.Continuum.BF4ExactSlabPlaquettePairPathCarrier.pathAnimal
#print axioms YMGap.Continuum.BF4ExactSlabPlaquettePairPathCarrier.pathAnimal_support_length_le
#print axioms YMGap.Continuum.BF4ExactSlabPlaquettePairPathCarrier.pairCarrier
#print axioms YMGap.Continuum.BF4ExactSlabPlaquettePairPathCarrier.pairCarrier_support_length_le
#print axioms YMGap.Continuum.BF4ExactSlabPlaquettePairPathCarrier.left_local_on_pair
#print axioms YMGap.Continuum.BF4ExactSlabPlaquettePairPathCarrier.right_local_on_pair
