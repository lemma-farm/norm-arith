import Examples.DiarHaidary__Sharp_Bounds_for_Graph_Matrices.Dependencies.vad36d74d65ba.GraphMatrices.Separators
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Data.Real.Basic
/-!
The exponents of report 96, defined from the actual connected components of
the graph remaining after vertex deletion. No analytic estimate is assumed.
-/
namespace GraphMatrices
variable {α : Type*} [Fintype α] [DecidableEq α]
def NoFloatingAt (G : SimpleGraph α) (S U : Finset α) : Prop :=
  ∀ C : (outsideGraph G S).ConnectedComponent, ∃ u ∈ C.supp, u.val ∈ U
theorem noFloatingAt_reaches {G : SimpleGraph α} {S U : Finset α}
    (hnf : NoFloatingAt G S U) (x : {x : α // x ∉ S}) :
    ∃ u : {x : α // x ∉ S}, u.val ∈ U ∧ (outsideGraph G S).Reachable x u := by
  obtain ⟨u, huC, huU⟩ := hnf ((outsideGraph G S).connectedComponentMk x)
  exact ⟨u, huU, (SimpleGraph.ConnectedComponent.exact huC).symm⟩
/-- The precise combinatorial source of the power saving in the side creation
Gram estimate: a nonempty changed-role set disjoint from the output boundary
has an unchanged neighbor outside the input boundary. -/
theorem changed_set_has_unchanged_neighbor {G : SimpleGraph α} {S U : Finset α}
    (hmin : IsMinimumSeparator G S U S) (hnf : NoFloatingAt G S U)
    (T : Finset α) (hne : T.Nonempty) (hTU : ∀ x ∈ T, x ∉ U) :
    ∃ x ∈ T, ∃ y, y ∉ T ∧ y ∉ S ∧ G.Adj x y := by
  classical
  by_contra hn
  obtain ⟨x, hxT⟩ := hne
  by_cases hxS : x ∈ S
  · have hsep : Separates G S U (S \ T) := by
      intro u v hu hv ⟨p⟩
      have huT : u.val ∈ T := by
        by_contra h
        exact u.property (Finset.mem_sdiff.2 ⟨hu, h⟩)
      have hclosed : ∀ {a b : {z : α // z ∉ S \ T}},
          (outsideGraph G (S \ T)).Adj a b → a.val ∈ T → b.val ∈ T := by
        intro a b hab ha
        by_contra hb
        have hbS : b.val ∈ S := by
          by_contra hbS
          exact hn ⟨a.val, ha, b.val, hb, hbS, hab⟩
        exact b.property (Finset.mem_sdiff.2 ⟨hbS, hb⟩)
      have hvT := walk_preserves_predicate hclosed p huT
      exact hTU v.val hvT hv
    have hstrict : S \ T ⊂ S := by
      apply Finset.ssubset_iff_subset_ne.2
      refine ⟨Finset.sdiff_subset, ?_⟩
      intro heq
      have hxST : x ∈ S \ T := heq.symm ▸ hxS
      exact (Finset.mem_sdiff.1 hxST).2 hxT
    have hcard := Finset.card_lt_card hstrict
    have hbound := separator_card_bound hsep
    have hsize := hmin.2
    omega
  · obtain ⟨u, huU, ⟨p⟩⟩ := noFloatingAt_reaches hnf ⟨x, hxS⟩
    have hclosed : ∀ {a b : {z : α // z ∉ S}},
        (outsideGraph G S).Adj a b → a.val ∈ T → b.val ∈ T := by
      intro a b hab ha
      by_contra hb
      exact hn ⟨a.val, ha, b.val, hb, b.property, hab⟩
    have huT := walk_preserves_predicate hclosed p hxT
    exact hTU u.val huT huU
theorem nonisolated_of_side_hypotheses {G : SimpleGraph α} {S U : Finset α}
    (hmin : IsMinimumSeparator G S U S) (hnf : NoFloatingAt G S U)
    {x : α} (hx : x ∉ U) : ∃ y, G.Adj x y := by
  classical
  obtain ⟨z, hz, y, _, _, hzy⟩ := changed_set_has_unchanged_neighbor hmin hnf {x}
    (Finset.singleton_nonempty x) (by intro z hz; simpa only [Finset.mem_singleton.1 hz] using hx)
  exact ⟨y, Finset.mem_singleton.1 hz ▸ hzy⟩
end GraphMatrices
