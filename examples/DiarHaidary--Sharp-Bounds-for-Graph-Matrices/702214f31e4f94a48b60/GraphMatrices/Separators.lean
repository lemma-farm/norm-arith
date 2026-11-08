import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.Powerset
import Mathlib.Tactic

/-!
Vertex separators with boundary vertices allowed, including zero-length paths.
The occupied-edge signature is the literal signature of report 97, Section 4.
-/

namespace GraphMatrices

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- The actual induced graph after removing the separator vertices. -/
abbrev outsideGraph (G : SimpleGraph α) (S : Finset α) :=
  G.induce {x | x ∉ S}

/-- No component of the graph outside S meets both boundaries.
The use of reachability includes paths of length zero. -/
def Separates (G : SimpleGraph α) (U V S : Finset α) : Prop :=
  ∀ (u v : {x : α // x ∉ S}), u.val ∈ U → v.val ∈ V →
    ¬ (outsideGraph G S).Reachable u v

theorem separates_univ (G : SimpleGraph α) (U V : Finset α) :
    Separates G U V Finset.univ := by
  intro u
  exact False.elim (u.property (Finset.mem_univ _))

theorem exists_separator_card (G : SimpleGraph α) (U V : Finset α) :
    ∃ k : ℕ, ∃ S : Finset α, Separates G U V S ∧ S.card = k :=
  ⟨Fintype.card α, Finset.univ, separates_univ G U V, Finset.card_univ⟩

/-- The minimum cardinality of a genuine vertex separator. -/
noncomputable def minimumSeparatorSize (G : SimpleGraph α) (U V : Finset α) : ℕ := by
  classical
  exact Nat.find (exists_separator_card G U V)

def IsMinimumSeparator (G : SimpleGraph α) (U V S : Finset α) : Prop :=
  Separates G U V S ∧ S.card = minimumSeparatorSize G U V

theorem exists_minimum_separator (G : SimpleGraph α) (U V : Finset α) :
    ∃ S, IsMinimumSeparator G U V S := by
  classical
  exact Nat.find_spec (exists_separator_card G U V)

theorem separator_card_bound {G : SimpleGraph α} {U V S : Finset α}
    (hS : Separates G U V S) :
    minimumSeparatorSize G U V ≤ S.card := by
  classical
  exact Nat.find_min' (exists_separator_card G U V) ⟨S, hS, rfl⟩

theorem minimumSeparatorSize_le_card (G : SimpleGraph α) (U V : Finset α) :
    minimumSeparatorSize G U V ≤ Fintype.card α := by
  simpa using separator_card_bound (separates_univ G U V)

/-- The finite, nonempty family over which the floating count is maximized. -/
noncomputable def minimumSeparators (G : SimpleGraph α) (U V : Finset α) :
    Finset (Finset α) := by
  classical
  exact Finset.univ.filter (IsMinimumSeparator G U V)

@[simp] theorem mem_minimumSeparators (G : SimpleGraph α) (U V S : Finset α) :
    S ∈ minimumSeparators G U V ↔ IsMinimumSeparator G U V S := by
  classical
  simp [minimumSeparators]

theorem minimumSeparators_nonempty (G : SimpleGraph α) (U V : Finset α) :
    (minimumSeparators G U V).Nonempty := by
  obtain ⟨S, hS⟩ := exists_minimum_separator G U V
  exact ⟨S, (mem_minimumSeparators G U V S).2 hS⟩

/-- Common boundary roles are forced by their paths of length zero. -/
theorem common_boundary_mem {G : SimpleGraph α} {U V S : Finset α}
    (hS : Separates G U V S) {x : α} (hxU : x ∈ U) (hxV : x ∈ V) :
    x ∈ S := by
  by_contra hxS
  exact hS ⟨x, hxS⟩ ⟨x, hxS⟩ hxU hxV (.refl _)

theorem common_boundary_subset {G : SimpleGraph α} {U V S : Finset α}
    (hS : Separates G U V S) : U ∩ V ⊆ S := by
  intro x hx
  exact common_boundary_mem hS (Finset.mem_inter.1 hx).1 (Finset.mem_inter.1 hx).2

theorem Separates.symm {G : SimpleGraph α} {U V S : Finset α}
    (hS : Separates G U V S) : Separates G V U S := by
  intro u v hu hv h
  exact hS v u hv hu h.symm

theorem minimumSeparatorSize_symm (G : SimpleGraph α) (U V : Finset α) :
    minimumSeparatorSize G U V = minimumSeparatorSize G V U := by
  obtain ⟨S, hS, hScard⟩ := exists_minimum_separator G U V
  obtain ⟨T, hT, hTcard⟩ := exists_minimum_separator G V U
  apply Nat.le_antisymm
  · exact hTcard ▸ separator_card_bound hT.symm
  · exact hScard ▸ separator_card_bound hS.symm

theorem IsMinimumSeparator.symm {G : SimpleGraph α} {U V S : Finset α}
    (hS : IsMinimumSeparator G U V S) : IsMinimumSeparator G V U S := by
  exact ⟨hS.1.symm, hS.2.trans (minimumSeparatorSize_symm G U V)⟩

theorem minimumSeparatorSize_ge_overlap (G : SimpleGraph α) (U V : Finset α) :
    (U ∩ V).card ≤ minimumSeparatorSize G U V := by
  obtain ⟨S, hS, hcard⟩ := exists_minimum_separator G U V
  rw [← hcard]
  exact Finset.card_le_card (common_boundary_subset hS)

theorem separates_left (G : SimpleGraph α) (U V : Finset α) :
    Separates G U V U := by
  intro u _ hu
  exact False.elim (u.property hu)

theorem separates_right (G : SimpleGraph α) (U V : Finset α) :
    Separates G U V V := by
  intro _ v _ hv
  exact False.elim (v.property hv)

theorem minimumSeparatorSize_le_left (G : SimpleGraph α) (U V : Finset α) :
    minimumSeparatorSize G U V ≤ U.card :=
  separator_card_bound (separates_left G U V)

theorem minimumSeparatorSize_le_right (G : SimpleGraph α) (U V : Finset α) :
    minimumSeparatorSize G U V ≤ V.card :=
  separator_card_bound (separates_right G U V)

@[simp] theorem minimumSeparatorSize_empty_left (G : SimpleGraph α) (V : Finset α) :
    minimumSeparatorSize G ∅ V = 0 :=
  Nat.eq_zero_of_le_zero (minimumSeparatorSize_le_left G ∅ V)

@[simp] theorem minimumSeparatorSize_empty_right (G : SimpleGraph α) (U : Finset α) :
    minimumSeparatorSize G U ∅ = 0 :=
  Nat.eq_zero_of_le_zero (minimumSeparatorSize_le_right G U ∅)

/-- The reachability definition is exactly the usual walk-hitting definition. -/
theorem separates_iff_walk_hits (G : SimpleGraph α) (U V S : Finset α) :
    Separates G U V S ↔
      ∀ u ∈ U, ∀ v ∈ V, ∀ p : G.Walk u v, ∃ x ∈ p.support, x ∈ S := by
  classical
  constructor
  · intro h u hu v hv p
    by_contra hn
    have havoid : ∀ x ∈ p.support, x ∉ S := by
      intro x hx hxS
      exact hn ⟨x, hx, hxS⟩
    exact h ⟨u, havoid u p.start_mem_support⟩ ⟨v, havoid v p.end_mem_support⟩ hu hv
      ⟨p.induce {x | x ∉ S} havoid⟩
  · intro h u v hu hv ⟨p⟩
    let q := p.map (SimpleGraph.Embedding.induce {x : α | x ∉ S}).toHom
    obtain ⟨x, hx, hxS⟩ := h u.val hu v.val hv q
    change x ∈ (p.map (SimpleGraph.Embedding.induce {x : α | x ∉ S}).toHom).support at hx
    rw [SimpleGraph.Walk.support_map] at hx
    obtain ⟨w, _, hw⟩ := List.mem_map.1 hx
    change w.val = x at hw
    exact w.property (hw.symm ▸ hxS)

/-- A component-by-component characterization of an actual separator. -/
theorem separates_iff_component_not_both (G : SimpleGraph α) (U V S : Finset α) :
    Separates G U V S ↔
      ∀ C : (outsideGraph G S).ConnectedComponent,
        ¬ ((∃ u ∈ C.supp, u.val ∈ U) ∧ (∃ v ∈ C.supp, v.val ∈ V)) := by
  constructor
  · intro h C ⟨⟨u, huC, hu⟩, ⟨v, hvC, hv⟩⟩
    exact h u v hu hv (SimpleGraph.ConnectedComponent.exact
      ((C.mem_supp_iff u).1 huC |>.trans ((C.mem_supp_iff v).1 hvC).symm))
  · intro h u v hu hv hp
    apply h ((outsideGraph G S).connectedComponentMk u)
    refine ⟨⟨u, rfl, hu⟩, v, ?_, hv⟩
    exact SimpleGraph.ConnectedComponent.sound hp.symm

/-- Deleting any vertex from a minimum separator destroys separation. -/
theorem minimum_separator_essential {G : SimpleGraph α} {U V S : Finset α}
    (hS : IsMinimumSeparator G U V S) {z : α} (hz : z ∈ S) :
    ¬ Separates G U V (S.erase z) := by
  intro herase
  have hmin := separator_card_bound herase
  have hcard := Finset.card_erase_lt_of_mem hz
  have hsize := hS.2
  omega

/-- Each vertex of a minimum separator has a boundary-to-boundary witness walk
that meets the separator only at that vertex. -/
theorem minimum_separator_witness {G : SimpleGraph α} {U V S : Finset α}
    (hS : IsMinimumSeparator G U V S) {z : α} (hz : z ∈ S) :
    ∃ u ∈ U, ∃ v ∈ V, ∃ p : G.Walk u v,
      z ∈ p.support ∧ ∀ x ∈ p.support, x ∈ S → x = z := by
  classical
  have hn := minimum_separator_essential hS hz
  rw [separates_iff_walk_hits] at hn
  push Not at hn
  obtain ⟨u, hu, v, hv, p, hp⟩ := hn
  have honly : ∀ x ∈ p.support, x ∈ S → x = z := by
    intro x hx hxS
    by_contra hneq
    exact hp x hx (Finset.mem_erase.2 ⟨hneq, hxS⟩)
  obtain ⟨x, hx, hxS⟩ := (separates_iff_walk_hits G U V S).1 hS.1 u hu v hv p
  exact ⟨u, hu, v, hv, p, (honly x hx hxS) ▸ hx, honly⟩

/-- A minimum-separator vertex belongs to a component meeting each boundary. -/
theorem minimum_separator_reaches_boundaries {G : SimpleGraph α} {U V S : Finset α}
    (hS : IsMinimumSeparator G U V S) {z : α} (hz : z ∈ S) :
    (∃ u ∈ U, G.Reachable z u) ∧ (∃ v ∈ V, G.Reachable z v) := by
  classical
  obtain ⟨u, hu, v, hv, p, hzp, _⟩ := minimum_separator_witness hS hz
  exact ⟨⟨u, hu, (p.takeUntil z hzp).reachable.symm⟩,
    ⟨v, hv, (p.dropUntil z hzp).reachable⟩⟩

/-- Vertices of an original component missing both boundaries cannot occur in
a minimum separator. It already suffices that the input boundary is unreachable. -/
theorem not_mem_minimum_separator_of_no_boundary_reach {G : SimpleGraph α}
    {U V S : Finset α} (hS : IsMinimumSeparator G U V S) {z : α}
    (hglobal : ∀ u ∈ U, ¬ G.Reachable z u) : z ∉ S := by
  intro hz
  obtain ⟨u, hu, hzu⟩ := (minimum_separator_reaches_boundaries hS hz).1
  exact hglobal u hu hzu

/-- A set closed under adjacency is closed under arbitrary finite walks. -/
theorem walk_preserves_predicate {β : Type*} {G : SimpleGraph β} {P : β → Prop}
    (hclosed : ∀ {x y}, G.Adj x y → P x → P y) {u v : β}
    (p : G.Walk u v) (hu : P u) : P v := by
  induction p with
  | nil => exact hu
  | cons h _ ih => exact ih (hclosed h hu)

/-- A preconnected finite graph has an actual edge crossing every nontrivial cut. -/
theorem preconnected_crosses_every_cut {G : SimpleGraph α} (hconn : G.Preconnected)
    (T : Finset α) (hne : T.Nonempty) (hproper : T ≠ Finset.univ) :
    ∃ x ∈ T, ∃ y ∉ T, G.Adj x y := by
  classical
  by_contra hn
  have hclosed : ∀ {x y}, G.Adj x y → x ∈ T → y ∈ T := by
    intro x y hxy hx
    by_contra hy
    exact hn ⟨x, hx, y, hy, hxy⟩
  obtain ⟨x, hx⟩ := hne
  apply hproper
  apply Finset.eq_univ_of_forall
  intro y
  obtain ⟨p⟩ := hconn x y
  exact walk_preserves_predicate hclosed p hx

/-- A boundary set restricted to an induced vertex set. -/
noncomputable def restrictBoundary (D A : Finset α) : Finset {x : α // x ∈ D} := by
  classical
  exact Finset.univ.filter (fun x => x.val ∈ A)

@[simp] theorem mem_restrictBoundary (D A : Finset α) (x : {x : α // x ∈ D}) :
    x ∈ restrictBoundary D A ↔ x.val ∈ A := by
  classical
  simp [restrictBoundary]

theorem image_restrictBoundary {D A : Finset α} (hA : A ⊆ D) :
    (restrictBoundary D A).image Subtype.val = A := by
  classical
  ext x
  constructor
  · intro hx
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.1 hx
    exact (mem_restrictBoundary D A y).1 hy
  · intro hx
    exact Finset.mem_image.2 ⟨⟨x, hA hx⟩, (mem_restrictBoundary D A _).2 hx, rfl⟩

theorem card_restrictBoundary {D A : Finset α} (hA : A ⊆ D) :
    (restrictBoundary D A).card = A.card := by
  classical
  calc
    (restrictBoundary D A).card = ((restrictBoundary D A).image Subtype.val).card :=
      (Finset.card_image_of_injective _ Subtype.val_injective).symm
    _ = A.card := congrArg Finset.card (image_restrictBoundary hA)

/-- For a graph supported on D, an induced-graph separator is also an ambient
separator after its labels are mapped back to the original vertex type. -/
theorem separates_induce_transfers {G : SimpleGraph α} {U V D : Finset α}
    (hU : U ⊆ D) (hV : V ⊆ D)
    (hclosed : ∀ {x y}, G.Adj x y → x ∈ D → y ∈ D)
    {T : Finset {x : α // x ∈ D}}
    (hT : Separates (G.induce {x | x ∈ D}) (restrictBoundary D U)
      (restrictBoundary D V) T) :
    Separates G U V (T.image Subtype.val) := by
  classical
  apply (separates_iff_walk_hits G U V _).2
  intro u hu v hv p
  have hsupport : ∀ x ∈ p.support, x ∈ D := by
    intro x hx
    exact walk_preserves_predicate hclosed (p.takeUntil x hx) (hU hu)
  let q := p.induce {x | x ∈ D} hsupport
  obtain ⟨x, hxq, hxT⟩ := (separates_iff_walk_hits (G.induce {x | x ∈ D})
    (restrictBoundary D U) (restrictBoundary D V) T).1 hT
      ⟨u, hsupport u p.start_mem_support⟩ ((mem_restrictBoundary D U _).2 hu)
      ⟨v, hsupport v p.end_mem_support⟩ ((mem_restrictBoundary D V _).2 hv) q
  have hxp : x.val ∈ p.support := by
    have hm : x.val ∈ (q.map (SimpleGraph.Embedding.induce {x : α | x ∈ D}).toHom).support := by
      rw [SimpleGraph.Walk.support_map]
      exact List.mem_map.2 ⟨x, hxq, rfl⟩
    have hmap : q.map (SimpleGraph.Embedding.induce {x : α | x ∈ D}).toHom = p :=
      SimpleGraph.Walk.map_induce p hsupport
    rw [hmap] at hm
    exact hm
  exact ⟨x.val, hxp, Finset.mem_image.2 ⟨x, hxT, rfl⟩⟩

/-- A two-region partition with no crossing edge gives an actual separator. -/
theorem separates_of_no_crossing {G : SimpleGraph α} {U V R Z : Finset α}
    (hUV : ∀ x ∈ U, x ∉ Z) (hVU : ∀ x ∈ V, x ∉ R)
    (hcross : ∀ x ∈ R, ∀ y ∈ Z, ¬ G.Adj x y) :
    Separates G U V (R ∪ Z)ᶜ := by
  classical
  intro u v hu hv hp
  have hm (x : {x : α // x ∉ (R ∪ Z)ᶜ}) : x.val ∈ R ∨ x.val ∈ Z := by
    simpa only [Finset.mem_compl, not_not, Finset.mem_union] using x.property
  have huR : u.val ∈ R := (hm u).resolve_right (hUV _ hu)
  have hvR : v.val ∈ R := by
    obtain ⟨p⟩ := hp
    apply walk_preserves_predicate (P := fun x => x.val ∈ R) ?_ p huR
    intro x y hxy hx
    exact (hm y).resolve_right (fun hy => hcross x.val hx y.val hy hxy)
  exact hVU _ hv hvR

/-- No isolated interior roles: boundary isolates remain permitted. -/
def NoIsolatedInterior (G : SimpleGraph α) (U V : Finset α) : Prop :=
  ∀ x, x ∉ U → x ∉ V → ∃ y, G.Adj x y

/-- Roles whose entire incident edge set is occupied.
The domain is the complement of the output boundary, so common roles stay out. -/
noncomputable def signatureR (G : SimpleGraph α) (V : Finset α)
    (F : Finset (Sym2 α)) : Finset α := by
  classical
  exact Finset.univ.filter (fun x => x ∉ V ∧ ∀ y, G.Adj x y → s(x, y) ∈ F)

/-- Roles whose entire incident edge set is unoccupied. -/
noncomputable def signatureZ (G : SimpleGraph α) (U : Finset α)
    (F : Finset (Sym2 α)) : Finset α := by
  classical
  exact Finset.univ.filter (fun x => x ∉ U ∧ ∀ y, G.Adj x y → s(x, y) ∉ F)

noncomputable def signatureS (G : SimpleGraph α) (U V : Finset α)
    (F : Finset (Sym2 α)) : Finset α :=
  (signatureR G V F ∪ signatureZ G U F)ᶜ

@[simp] theorem mem_signatureR (G : SimpleGraph α) (V : Finset α)
    (F : Finset (Sym2 α)) (x : α) :
    x ∈ signatureR G V F ↔ x ∉ V ∧ ∀ y, G.Adj x y → s(x, y) ∈ F := by
  classical
  simp [signatureR]

@[simp] theorem mem_signatureZ (G : SimpleGraph α) (U : Finset α)
    (F : Finset (Sym2 α)) (x : α) :
    x ∈ signatureZ G U F ↔ x ∉ U ∧ ∀ y, G.Adj x y → s(x, y) ∉ F := by
  classical
  simp [signatureZ]

theorem signature_no_crossing (G : SimpleGraph α) (U V : Finset α)
    (F : Finset (Sym2 α)) :
    ∀ x ∈ signatureR G V F, ∀ y ∈ signatureZ G U F, ¬ G.Adj x y := by
  intro x hx y hy hxy
  have hF := ((mem_signatureR G V F x).1 hx).2 y hxy
  exact ((mem_signatureZ G U F y).1 hy).2 x hxy.symm (by simpa [Sym2.eq_swap] using hF)

/-- Every occupied-edge signature gives a separator, even if isolated interiors
are present. The disjointness/cardinality assertion below uses their exclusion. -/
theorem signature_separator (G : SimpleGraph α) (U V : Finset α)
    (F : Finset (Sym2 α)) : Separates G U V (signatureS G U V F) := by
  apply separates_of_no_crossing
  · intro x hx hxZ
    exact ((mem_signatureZ G U F x).1 hxZ).1 hx
  · intro x hx hxR
    exact ((mem_signatureR G V F x).1 hxR).1 hx
  · exact signature_no_crossing G U V F

theorem signature_outside_mem_union (G : SimpleGraph α) (U V : Finset α)
    (F : Finset (Sym2 α)) (x : {x : α // x ∉ signatureS G U V F}) :
    x.val ∈ signatureR G V F ∨ x.val ∈ signatureZ G U F := by
  simpa only [signatureS, Finset.mem_compl, not_not, Finset.mem_union] using x.property

theorem signature_walk_preserves_R (G : SimpleGraph α) (U V : Finset α)
    (F : Finset (Sym2 α)) {x y : {x : α // x ∉ signatureS G U V F}}
    (hxy : (outsideGraph G (signatureS G U V F)).Reachable x y)
    (hx : x.val ∈ signatureR G V F) : y.val ∈ signatureR G V F := by
  obtain ⟨p⟩ := hxy
  apply walk_preserves_predicate (P := fun z => z.val ∈ signatureR G V F) ?_ p hx
  intro a b hab ha
  exact (signature_outside_mem_union G U V F b).resolve_right
    (fun hb => signature_no_crossing G U V F a.val ha b.val hb hab)

theorem signature_walk_preserves_Z (G : SimpleGraph α) (U V : Finset α)
    (F : Finset (Sym2 α)) {x y : {x : α // x ∉ signatureS G U V F}}
    (hxy : (outsideGraph G (signatureS G U V F)).Reachable x y)
    (hx : x.val ∈ signatureZ G U F) : y.val ∈ signatureZ G U F := by
  obtain ⟨p⟩ := hxy
  apply walk_preserves_predicate (P := fun z => z.val ∈ signatureZ G U F) ?_ p hx
  intro a b hab ha
  exact (signature_outside_mem_union G U V F b).resolve_left
    (fun hb => signature_no_crossing G U V F b.val hb a.val ha hab.symm)

/-- Every component of the signature-deleted graph lies entirely on one
occupation side. This includes the floating components. -/
theorem signature_component_monochromatic (G : SimpleGraph α) (U V : Finset α)
    (F : Finset (Sym2 α))
    (C : (outsideGraph G (signatureS G U V F)).ConnectedComponent) :
    (∀ x ∈ C.supp, x.val ∈ signatureR G V F) ∨
      (∀ x ∈ C.supp, x.val ∈ signatureZ G U F) := by
  obtain ⟨x, hxC⟩ := C.nonempty_supp
  have hreach : ∀ y ∈ C.supp, (outsideGraph G (signatureS G U V F)).Reachable x y := by
    intro y hyC
    exact SimpleGraph.ConnectedComponent.exact (((C.mem_supp_iff x).1 hxC).trans
      ((C.mem_supp_iff y).1 hyC).symm)
  obtain hxR | hxZ := signature_outside_mem_union G U V F x
  · exact Or.inl (fun y hy => signature_walk_preserves_R G U V F (hreach y hy) hxR)
  · exact Or.inr (fun y hy => signature_walk_preserves_Z G U V F (hreach y hy) hxZ)

theorem signature_input_component_in_R (G : SimpleGraph α) (U V : Finset α)
    (F : Finset (Sym2 α)) (C : (outsideGraph G (signatureS G U V F)).ConnectedComponent)
    (hmeet : ∃ u ∈ C.supp, u.val ∈ U) :
    ∀ x ∈ C.supp, x.val ∈ signatureR G V F := by
  obtain hR | hZ := signature_component_monochromatic G U V F C
  · exact hR
  · obtain ⟨u, huC, huU⟩ := hmeet
    exact False.elim (((mem_signatureZ G U F u.val).1 (hZ u huC)).1 huU)

theorem signature_output_component_in_Z (G : SimpleGraph α) (U V : Finset α)
    (F : Finset (Sym2 α)) (C : (outsideGraph G (signatureS G U V F)).ConnectedComponent)
    (hmeet : ∃ u ∈ C.supp, u.val ∈ V) :
    ∀ x ∈ C.supp, x.val ∈ signatureZ G U F := by
  obtain hR | hZ := signature_component_monochromatic G U V F C
  · obtain ⟨u, huC, huV⟩ := hmeet
    exact False.elim (((mem_signatureR G V F u.val).1 (hR u huC)).1 huV)
  · exact hZ

theorem signature_disjoint {G : SimpleGraph α} {U V : Finset α}
    (hNI : NoIsolatedInterior G U V) (F : Finset (Sym2 α)) :
    Disjoint (signatureR G V F) (signatureZ G U F) := by
  rw [Finset.disjoint_left]
  intro x hxR hxZ
  obtain ⟨hxV, hR⟩ := (mem_signatureR G V F x).1 hxR
  obtain ⟨hxU, hZ⟩ := (mem_signatureZ G U F x).1 hxZ
  obtain ⟨y, hxy⟩ := hNI x hxU hxV
  exact hZ y hxy (hR y hxy)

theorem signature_card_partition {G : SimpleGraph α} {U V : Finset α}
    (hNI : NoIsolatedInterior G U V) (F : Finset (Sym2 α)) :
    (signatureR G V F).card + (signatureZ G U F).card +
      (signatureS G U V F).card = Fintype.card α := by
  classical
  rw [← Finset.card_union_of_disjoint (signature_disjoint hNI F)]
  exact Finset.card_add_card_compl _

/-- The structural counting bound used before the critical-pattern split. -/
theorem signature_card_bound {G : SimpleGraph α} {U V : Finset α}
    (hNI : NoIsolatedInterior G U V) (F : Finset (Sym2 α)) :
    (signatureR G V F).card + (signatureZ G U F).card ≤
      Fintype.card α - minimumSeparatorSize G U V := by
  have hpart := signature_card_partition hNI F
  have hsep := separator_card_bound (signature_separator G U V F)
  omega

/-- Equality in the counting bound means that the actual signature separator
has minimum cardinality. -/
theorem signature_critical_iff {G : SimpleGraph α} {U V : Finset α}
    (hNI : NoIsolatedInterior G U V) (F : Finset (Sym2 α)) :
    (signatureR G V F).card + (signatureZ G U F).card =
      Fintype.card α - minimumSeparatorSize G U V ↔
      IsMinimumSeparator G U V (signatureS G U V F) := by
  have hpart := signature_card_partition hNI F
  have hbound := minimumSeparatorSize_le_card G U V
  constructor
  · intro h
    exact ⟨signature_separator G U V F, by omega⟩
  · rintro ⟨_, h⟩
    omega

end GraphMatrices
