import Examples.DiarHaidary__Sharp_Bounds_for_Graph_Matrices.Dependencies.vad36d74d65ba.GraphMatrices.SpectralNorm
import Examples.DiarHaidary__Sharp_Bounds_for_Graph_Matrices.Dependencies.vad36d74d65ba.GraphMatrices.Separators
import Mathlib.Data.Finset.Powerset
/-!
# Finite occupation creation and annihilation

Every occupation state is a literal finite subset of the finite primitive-edge
type. The matrices below are ordinary real matrices and consequently use the
Euclidean operator interpretation established in `SpectralNorm`.
-/
namespace GraphMatrices.OccupationCreation
noncomputable section
attribute [local instance] Classical.propDecidable
open scoped BigOperators
variable {E : Type*} [Fintype E] [DecidableEq E]
/-- The finite coordinate type for the occupation Hilbert space. -/
abbrev State (E : Type*) := Finset E
/-- The matrix of a deterministic transition that may be disabled at its source. -/
def transition (enabled : State E → Prop) [DecidablePred enabled]
    (next : State E → State E) :
    Matrix (State E) (State E) ℝ :=
  fun target source => if enabled source ∧ target = next source then 1 else 0
theorem transition_mul_apply
    (p q : State E → Prop) [DecidablePred p] [DecidablePred q]
    (f g : State E → State E) (target source : State E) :
    (transition p f * transition q g) target source =
      if q source ∧ p (g source) ∧ target = f (g source) then 1 else 0 := by
  classical
  rw [Matrix.mul_apply]
  rw [Finset.sum_eq_single (g source)]
  · simp only [transition]
    by_cases hq : q source <;> by_cases hp : p (g source) <;>
      by_cases ht : target = f (g source) <;> simp [hq, hp, ht]
  · intro intermediate _ hne
    simp [transition, hne]
  · simp
/-- Creation adds the complete edge set exactly when all its edges are unoccupied. -/
def creationAtom (A : Finset E) : Matrix (State E) (State E) ℝ :=
  transition (Disjoint A) (fun source => source ∪ A)
/-- Annihilation removes the complete edge set exactly when all its edges are occupied. -/
def annihilationAtom (A : Finset E) : Matrix (State E) (State E) ℝ :=
  transition (fun source => A ⊆ source) (fun source => source \ A)
@[simp] theorem creationAtom_apply (A target source : Finset E) :
    creationAtom A target source =
      if Disjoint A source ∧ target = source ∪ A then 1 else 0 := rfl
@[simp] theorem annihilationAtom_apply (A target source : Finset E) :
    annihilationAtom A target source =
      if A ⊆ source ∧ target = source \ A then 1 else 0 := rfl
theorem add_remove_relation (A target source : Finset E) :
    (Disjoint A target ∧ source = target ∪ A) ↔
      (A ⊆ source ∧ target = source \ A) := by
  constructor
  · rintro ⟨hd, rfl⟩
    constructor
    · exact Finset.subset_union_right
    · apply Finset.ext
      intro x
      have hdis := Finset.disjoint_left.mp hd
      simp only [Finset.mem_union, Finset.mem_sdiff]
      constructor
      · intro hx
        exact ⟨Or.inl hx, fun ha => hdis ha hx⟩
      · intro hx
        exact hx.1.resolve_right hx.2
  · rintro ⟨hs, rfl⟩
    constructor
    · apply Finset.disjoint_left.mpr
      intro x hx hxS
      exact (Finset.mem_sdiff.mp hxS).2 hx
    · exact (Finset.sdiff_union_of_subset hs).symm
/-- Literal transpose is annihilation; no adjoint relation is postulated. -/
@[simp] theorem creationAtom_transpose (A : Finset E) :
    (creationAtom A).transpose = annihilationAtom A := by
  ext target source
  simp only [Matrix.transpose_apply, creationAtom_apply, annihilationAtom_apply]
  simp only [add_remove_relation]
@[simp] theorem annihilationAtom_transpose (A : Finset E) :
    (annihilationAtom A).transpose = creationAtom A := by
  rw [← creationAtom_transpose, Matrix.transpose_transpose]
/-- The exact add-then-remove coefficient, including its output state. -/
theorem annihilation_creation_apply (A B target source : Finset E) :
    (annihilationAtom A * creationAtom B) target source =
      if Disjoint B source ∧ A ⊆ source ∪ B ∧ target = (source ∪ B) \ A
      then 1 else 0 :=
  transition_mul_apply _ _ _ _ _ _
/-- The exact remove-then-add coefficient, including its output state. -/
theorem creation_annihilation_apply (A B target source : Finset E) :
    (creationAtom B * annihilationAtom A) target source =
      if A ⊆ source ∧ Disjoint B (source \ A) ∧ target = (source \ A) ∪ B
      then 1 else 0 :=
  transition_mul_apply _ _ _ _ _ _
theorem disjoint_add_remove_conditions (A B source : Finset E) (hAB : Disjoint A B) :
    (Disjoint B source ∧ A ⊆ source ∪ B) ↔
      (A ⊆ source ∧ Disjoint B (source \ A)) := by
  constructor
  · rintro ⟨hB, hA⟩
    constructor
    · intro x hx
      rcases Finset.mem_union.mp (hA hx) with hxS | hxB
      · exact hxS
      · exact False.elim (Finset.disjoint_left.mp hAB hx hxB)
    · exact hB.mono_right Finset.sdiff_subset
  · rintro ⟨hA, hB⟩
    constructor
    · apply Finset.disjoint_left.mpr
      intro x hxB hxS
      by_cases hxA : x ∈ A
      · exact Finset.disjoint_left.mp hAB hxA hxB
      · exact Finset.disjoint_left.mp hB hxB (Finset.mem_sdiff.mpr ⟨hxS, hxA⟩)
    · exact hA.trans Finset.subset_union_left
theorem disjoint_add_remove_target (A B source : Finset E) (hAB : Disjoint A B) :
    (source ∪ B) \ A = (source \ A) ∪ B := by
  ext x
  have hdis := Finset.disjoint_left.mp hAB
  simp only [Finset.mem_union, Finset.mem_sdiff]
  constructor
  · rintro ⟨hxS | hxB, hxA⟩
    · exact Or.inl ⟨hxS, hxA⟩
    · exact Or.inr hxB
  · rintro (⟨hxS, hxA⟩ | hxB)
    · exact ⟨Or.inl hxS, hxA⟩
    · exact ⟨Or.inr hxB, fun hxA => hdis hxA hxB⟩
/-- Annihilation of A and creation of disjoint B commute exactly. -/
theorem disjoint_annihilation_creation (A B : Finset E) (hAB : Disjoint A B) :
    annihilationAtom A * creationAtom B = creationAtom B * annihilationAtom A := by
  ext target source
  rw [annihilation_creation_apply, creation_annihilation_apply,
    disjoint_add_remove_target A B source hAB]
  have hconditions := disjoint_add_remove_conditions A B source hAB
  simp only [← and_assoc]
  simp only [hconditions]
variable {ι : Type*} [Fintype ι]
/-- Creation for a family of embeddings; repeated edge sets retain multiplicity. -/
def creation (edges : ι → Finset E) : Matrix (State E) (State E) ℝ :=
  ∑ i, creationAtom (edges i)
/-- Annihilation for the same family, with identical multiplicities. -/
def annihilation (edges : ι → Finset E) : Matrix (State E) (State E) ℝ :=
  ∑ i, annihilationAtom (edges i)
@[simp] theorem creation_transpose (edges : ι → Finset E) :
    (creation edges).transpose = annihilation edges := by
  simp [creation, annihilation, Matrix.transpose_sum]
/-- Nonempty creations strictly raise the occupation grade. -/
theorem creation_zero_of_card_le (edges : ι → Finset E)
    (hne : ∀ i, (edges i).Nonempty) (target source : State E)
    (hcard : target.card ≤ source.card) : creation edges target source = 0 := by
  classical
  simp only [creation, Matrix.sum_apply]
  apply Finset.sum_eq_zero
  intro i _
  by_cases h : Disjoint (edges i) source ∧ target = source ∪ edges i
  · have hc : target.card = source.card + (edges i).card := by
      rw [h.2, Finset.card_union_of_disjoint h.1.symm]
    have he : 0 < (edges i).card := (hne i).card_pos
    omega
  · simp [h]
/-- A homogeneous creator changes the grade by exactly the embedding edge count. -/
theorem creation_zero_of_card_ne (edges : ι → Finset E) {e : ℕ}
    (he : ∀ i, (edges i).card = e) (target source : State E)
    (hcard : target.card ≠ source.card + e) : creation edges target source = 0 := by
  classical
  simp only [creation, Matrix.sum_apply]
  apply Finset.sum_eq_zero
  intro i _
  by_cases h : Disjoint (edges i) source ∧ target = source ∪ edges i
  · have hc : target.card = source.card + e := by
      rw [h.2, Finset.card_union_of_disjoint h.1.symm, he i]
    exact False.elim (hcard hc)
  · simp [h]
variable {F : Type*} [Fintype F] [DecidableEq F]
/-- Restrict an arbitrary ambient occupation to a faithfully embedded edge universe. -/
def pullback (e : E ↪ F) (Ω : Finset F) : Finset E :=
  Finset.univ.filter (fun x => e x ∈ Ω)
@[simp] theorem mem_pullback (e : E ↪ F) (Ω : Finset F) (x : E) :
    x ∈ pullback e Ω ↔ e x ∈ Ω := by simp [pullback]
@[simp] theorem pullback_image (e : E ↪ F) (A : Finset E) :
    pullback e (A.image e) = A := by
  ext x
  simp [e.injective.eq_iff]
theorem image_disjoint_iff (e : E ↪ F) (A : Finset E) (Ω : Finset F) :
    Disjoint (A.image e) Ω ↔ Disjoint A (pullback e Ω) := by
  constructor
  · intro h
    apply Finset.disjoint_left.mpr
    intro x hx hΩ
    exact Finset.disjoint_left.mp h (Finset.mem_image.mpr ⟨x, hx, rfl⟩)
      ((mem_pullback e Ω x).1 hΩ)
  · intro h
    apply Finset.disjoint_left.mpr
    intro y hy hΩ
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hy
    exact Finset.disjoint_left.mp h hx ((mem_pullback e Ω x).2 hΩ)
theorem image_subset_iff (e : E ↪ F) (A : Finset E) (Ω : Finset F) :
    A.image e ⊆ Ω ↔ A ⊆ pullback e Ω := by
  constructor
  · intro h x hx
    exact (mem_pullback e Ω x).2 (h (Finset.mem_image.mpr ⟨x, hx, rfl⟩))
  · intro h y hy
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hy
    exact (mem_pullback e Ω x).1 (h hx)
@[simp] theorem pullback_union_image (e : E ↪ F) (Ω : Finset F) (A : Finset E) :
    pullback e (Ω ∪ A.image e) = pullback e Ω ∪ A := by
  ext x
  simp [e.injective.eq_iff]
@[simp] theorem pullback_sdiff_image (e : E ↪ F) (Ω : Finset F) (A : Finset E) :
    pullback e (Ω \ A.image e) = pullback e Ω \ A := by
  ext x
  simp [e.injective.eq_iff]
theorem card_pullback_le (e : E ↪ F) (Ω : Finset F) : (pullback e Ω).card ≤ Ω.card := by
  have hsubset : (pullback e Ω).image e ⊆ Ω :=
    (image_subset_iff e _ Ω).2 (Finset.Subset.refl _)
  have h := Finset.card_le_card hsubset
  simpa only [Finset.card_image_of_injective _ e.injective] using h
end
namespace Colored
noncomputable section
attribute [local instance] Classical.propDecidable
variable {C D : Type*} [Fintype C] [DecidableEq C] [Fintype D] [DecidableEq D]
/-- Fixed root labels are omitted; an edge records only its interior endpoints.
In a simple rooted graph each endpoint set has cardinal one or two. -/
abbrev Primitive (incident : D → Finset C) (n : ℕ) :=
  (d : D) × ({x // x ∈ incident d} → Fin n)
/-- The primitive edge generated by one colored interior assignment. -/
def primitive (incident : D → Finset C) {n : ℕ} (φ : C → Fin n) (d : D) :
    Primitive incident n := ⟨d, fun x => φ x⟩
/-- Complete primitive-edge set of an assignment; abstract edge roles are retained. -/
def edges (incident : D → Finset C) {n : ℕ} (φ : C → Fin n) :
    Finset (Primitive incident n) := by
  classical
  exact Finset.univ.image (primitive incident φ)
theorem primitive_injective (incident : D → Finset C) {n : ℕ} (φ : C → Fin n) :
    Function.Injective (primitive incident φ) := by
  intro d e h
  exact congrArg Sigma.fst h
theorem primitive_eq_iff (incident : D → Finset C) {n : ℕ}
    (φ ψ : C → Fin n) (d : D) :
    primitive incident φ d = primitive incident ψ d ↔
      ∀ x ∈ incident d, φ x = ψ x := by
  constructor
  · intro h x hx
    have hh := eq_of_heq (Sigma.mk.inj h).2
    exact congrFun hh ⟨x, hx⟩
  · intro h
    exact congrArg (Sigma.mk d) (funext fun x => h x x.property)
theorem primitive_mem_edges_iff (incident : D → Finset C) {n : ℕ}
    (φ ψ : C → Fin n) (d : D) :
    primitive incident ψ d ∈ edges incident φ ↔
      ∀ x ∈ incident d, ψ x = φ x := by
  classical
  constructor
  · intro h
    obtain ⟨e, _, he⟩ := Finset.mem_image.mp h
    have hed : e = d := congrArg Sigma.fst he
    subst e
    exact (primitive_eq_iff incident ψ φ d).1 he.symm
  · intro h
    apply Finset.mem_image.mpr
    exact ⟨d, Finset.mem_univ d, (primitive_eq_iff incident φ ψ d).2
      (fun x hx => (h x hx).symm)⟩
@[simp] theorem card_edges (incident : D → Finset C) {n : ℕ} (φ : C → Fin n) :
    (edges incident φ).card = Fintype.card D := by
  classical
  simp [edges, Finset.card_image_of_injective _ (primitive_injective incident φ)]
/-- Occupied interior-role/label pairs, including arbitrary occupied primitive edges. -/
def support (incident : D → Finset C) {n : ℕ}
    (Ω : Finset (Primitive incident n)) : Finset (C × Fin n) := by
  classical
  exact Ω.biUnion (fun p => Finset.univ.image (fun x => (x.val, p.2 x)))
theorem endpoint_mem_support (incident : D → Finset C) {n : ℕ}
    (Ω : Finset (Primitive incident n)) (p : Primitive incident n) (hp : p ∈ Ω)
    (x : C) (hx : x ∈ incident p.1) : (x, p.2 ⟨x, hx⟩) ∈ support incident Ω := by
  classical
  apply Finset.mem_biUnion.mpr
  refine ⟨p, hp, ?_⟩
  exact Finset.mem_image.mpr ⟨⟨x, hx⟩, Finset.mem_univ _, rfl⟩
/-- In a graph, k occupied primitive edges support at most 2k interior labels. -/
theorem card_support_le (incident : D → Finset C)
    (hdegree : ∀ d, (incident d).card ≤ 2) {n : ℕ}
    (Ω : Finset (Primitive incident n)) : (support incident Ω).card ≤ 2 * Ω.card := by
  classical
  unfold support
  calc
    _ ≤ ∑ p ∈ Ω, (Finset.univ.image (fun x => (x.val, p.2 x))).card :=
      Finset.card_biUnion_le
    _ ≤ ∑ p ∈ Ω, 2 := by
      apply Finset.sum_le_sum
      intro p _
      calc
        _ ≤ Fintype.card {x // x ∈ incident p.1} := by
          simpa using Finset.card_image_le (s := Finset.univ)
            (f := fun (x : {x // x ∈ incident p.1}) => (x.val, p.2 x))
        _ = (incident p.1).card := Fintype.card_coe _
        _ ≤ 2 := hdegree p.1
    _ = 2 * Ω.card := by simp [Nat.mul_comm]
/-- A changed endpoint forces the removed copy of its incident edge to be old. -/
theorem changed_edge_is_occupied (incident : D → Finset C) {n : ℕ}
    (φ ψ : C → Fin n) (Ω : Finset (Primitive incident n))
    (hremove : edges incident ψ ⊆ Ω ∪ edges incident φ)
    (d : D) (x : C) (hx : x ∈ incident d) (hchanged : φ x ≠ ψ x) :
    primitive incident ψ d ∈ Ω := by
  classical
  have hmem : primitive incident ψ d ∈ edges incident ψ :=
    (primitive_mem_edges_iff incident ψ ψ d).2 (fun _ _ => rfl)
  rcases Finset.mem_union.mp (hremove hmem) with hold | hnew
  · exact hold
  · exact False.elim (hchanged ((primitive_mem_edges_iff incident φ ψ d).1 hnew x hx).symm)
/-- Every changed removed label is supported on old occupied edges. -/
theorem changed_label_is_supported (incident : D → Finset C)
    (hincident : ∀ x, ∃ d, x ∈ incident d) {n : ℕ}
    (φ ψ : C → Fin n) (Ω : Finset (Primitive incident n))
    (hremove : edges incident ψ ⊆ Ω ∪ edges incident φ)
    (x : C) (hchanged : φ x ≠ ψ x) :
    (x, ψ x) ∈ support incident Ω := by
  obtain ⟨d, hd⟩ := hincident x
  exact endpoint_mem_support incident Ω (primitive incident ψ d)
    (changed_edge_is_occupied incident φ ψ Ω hremove d x hd hchanged) x hd
/-- Connectivity of the induced interior graph, stated as an exact finite cut property. -/
def CrossesEveryCut (incident : D → Finset C) : Prop :=
  ∀ T : Finset C, T.Nonempty → T ≠ Finset.univ →
    ∃ (d : D) (x y : C), x ∈ T ∧ y ∉ T ∧ x ∈ incident d ∧ y ∈ incident d
/-- The finite cut hypothesis follows from the actual induced graph's connectedness. -/
theorem crossesEveryCut_of_preconnected (G : SimpleGraph C) (hG : G.Preconnected)
    (incident : D → Finset C)
    (hedges : ∀ x y, G.Adj x y → ∃ d, x ∈ incident d ∧ y ∈ incident d) :
    CrossesEveryCut incident := by
  intro T hne hproper
  obtain ⟨x, hx, y, hy, hxy⟩ := GraphMatrices.preconnected_crosses_every_cut hG T hne hproper
  obtain ⟨d, hxd, hyd⟩ := hedges x y hxy
  exact ⟨d, x, y, hx, hy, hxd, hyd⟩
/-- The changed-role set used in the connected commutator count. -/
def changedRoles {n : ℕ} (φ ψ : C → Fin n) : Finset C :=
  Finset.univ.filter (fun x => φ x ≠ ψ x)
@[simp] theorem mem_changedRoles {n : ℕ} (φ ψ : C → Fin n) (x : C) :
    x ∈ changedRoles φ ψ ↔ φ x ≠ ψ x := by
  simp [changedRoles]
/-- Connectivity forces one unchanged creation label into the old support.
This is the actual mechanism saving one power of the ambient label count. -/
theorem unchanged_label_is_supported (incident : D → Finset C)
    (hconnected : CrossesEveryCut incident) {n : ℕ}
    (φ ψ : C → Fin n) (Ω : Finset (Primitive incident n))
    (hremove : edges incident ψ ⊆ Ω ∪ edges incident φ)
    (hchanged : (changedRoles φ ψ).Nonempty)
    (hproper : changedRoles φ ψ ≠ Finset.univ) :
    ∃ y, φ y = ψ y ∧ (y, φ y) ∈ support incident Ω := by
  obtain ⟨d, x, y, hx, hy, hxd, hyd⟩ := hconnected _ hchanged hproper
  have hyEq : φ y = ψ y := by simpa using hy
  have hOccupied := changed_edge_is_occupied incident φ ψ Ω hremove d x hxd
    ((mem_changedRoles φ ψ x).1 hx)
  refine ⟨y, hyEq, ?_⟩
  rw [hyEq]
  exact endpoint_mem_support incident Ω (primitive incident ψ d) hOccupied y hyd
/-- Distinct assignments have at least one changed role. -/
theorem changedRoles_nonempty_of_ne {n : ℕ} (φ ψ : C → Fin n) (h : φ ≠ ψ) :
    (changedRoles φ ψ).Nonempty := by
  classical
  contrapose! h
  funext x
  have hx : x ∉ changedRoles φ ψ := by rw [h]; simp
  simpa using hx
/-- A common primitive edge yields an unchanged interior role because root-only
edges have been excluded. -/
theorem exists_equal_of_not_disjoint (incident : D → Finset C)
    (hne : ∀ d, (incident d).Nonempty) {n : ℕ} (φ ψ : C → Fin n)
    (h : ¬ Disjoint (edges incident φ) (edges incident ψ)) : ∃ x, φ x = ψ x := by
  classical
  rw [Finset.not_disjoint_iff] at h
  obtain ⟨p, hpφ, hpψ⟩ := h
  obtain ⟨d, _, hd⟩ := Finset.mem_image.mp hpφ
  rw [← hd] at hpψ
  obtain ⟨x, hx⟩ := hne d
  exact ⟨x, (primitive_mem_edges_iff incident ψ φ d).1 hpψ x hx⟩
theorem changedRoles_ne_univ_of_not_disjoint (incident : D → Finset C)
    (hne : ∀ d, (incident d).Nonempty) {n : ℕ} (φ ψ : C → Fin n)
    (h : ¬ Disjoint (edges incident φ) (edges incident ψ)) :
    changedRoles φ ψ ≠ Finset.univ := by
  obtain ⟨x, hx⟩ := exists_equal_of_not_disjoint incident hne φ ψ h
  intro hu
  have hm : x ∈ changedRoles φ ψ := hu ▸ Finset.mem_univ x
  exact (mem_changedRoles φ ψ x).1 hm hx
/-- Every label of a completely removed embedding lies in the occupied support. -/
theorem removed_label_is_supported (incident : D → Finset C)
    (hincident : ∀ x, ∃ d, x ∈ incident d) {n : ℕ}
    (ψ : C → Fin n) (Ω : Finset (Primitive incident n))
    (hremove : edges incident ψ ⊆ Ω) (x : C) :
    (x, ψ x) ∈ support incident Ω := by
  obtain ⟨d, hd⟩ := hincident x
  apply endpoint_mem_support incident Ω (primitive incident ψ d)
    (hremove ((primitive_mem_edges_iff incident ψ ψ d).2 (fun _ _ => rfl))) x hd
/-- Assignments satisfying the support restrictions forced by the add/remove order. -/
abbrev AddSupportedPairs {n : ℕ} (S : Finset (C × Fin n)) :=
  {p : (C → Fin n) × (C → Fin n) //
    (∀ x, p.1 x ≠ p.2 x → (x, p.2 x) ∈ S) ∧ ∃ y, (y, p.1 y) ∈ S}
/-- A finite lossless code for an add/remove pair. The selected old label and
all changed removed labels belong to the explicitly enumerated support. -/
abbrev AddCode {n : ℕ} (S : Finset (C × Fin n)) :=
  (y : C) × (({x // x ≠ y} → Fin n) × S × (C → Option S))
def encodeAdd {n : ℕ} (S : Finset (C × Fin n)) (p : AddSupportedPairs S) :
    AddCode S := by
  classical
  let y := p.property.2.choose
  exact ⟨y, (fun x => p.val.1 x), ⟨(y, p.val.1 y), p.property.2.choose_spec⟩,
    fun x => if h : p.val.1 x = p.val.2 x then none
      else some ⟨(x, p.val.2 x), p.property.1 x h⟩⟩
def decodeAdd {n : ℕ} (S : Finset (C × Fin n)) (p : AddCode S) :
    (C → Fin n) × (C → Fin n) := by
  classical
  let φ : C → Fin n := fun x => if h : x = p.1 then p.2.2.1.val.2 else p.2.1 ⟨x, h⟩
  exact ⟨φ, fun x => match p.2.2.2 x with
    | none => φ x
    | some z => z.val.2⟩
theorem decode_encodeAdd {n : ℕ} (S : Finset (C × Fin n)) (p : AddSupportedPairs S) :
    decodeAdd S (encodeAdd S p) = p.val := by
  classical
  apply Prod.ext
  · funext x
    by_cases hx : x = p.property.2.choose
    · simp [decodeAdd, encodeAdd, hx]
    · simp [decodeAdd, encodeAdd, hx]
  · funext x
    by_cases heq : p.val.1 x = p.val.2 x
    · by_cases hx : x = p.property.2.choose
      · subst x
        simp [decodeAdd, encodeAdd, heq]
      · simp [decodeAdd, encodeAdd, heq, hx]
    · simp [decodeAdd, encodeAdd, heq]
theorem encodeAdd_injective {n : ℕ} (S : Finset (C × Fin n)) :
    Function.Injective (encodeAdd S) := by
  intro p q h
  apply Subtype.ext
  simpa only [decode_encodeAdd] using congrArg (decodeAdd S) h
/-- Concrete enumeration bound, obtained by the preceding injective code. -/
theorem card_addSupportedPairs_le {n : ℕ} (S : Finset (C × Fin n)) :
    Fintype.card (AddSupportedPairs S) ≤
      Fintype.card C * n ^ (Fintype.card C - 1) * S.card *
        (S.card + 1) ^ Fintype.card C := by
  classical
  calc
    _ ≤ Fintype.card (AddCode S) := Fintype.card_le_of_injective _ (encodeAdd_injective S)
    _ = _ := by
      simp [AddCode, Fintype.card_sigma, Fintype.card_prod, Fintype.card_fun,
        Fintype.card_subtype_compl, Fintype.card_subtype_eq, Fintype.card_coe,
        Nat.mul_assoc]
/-- Support restrictions for the remove/add order: the removed assignment is old
at every role, and the created assignment shares an interior label with it. -/
abbrev RemoveSupportedPairs {n : ℕ} (S : Finset (C × Fin n)) :=
  {p : (C → Fin n) × (C → Fin n) //
    (∀ x, (x, p.2 x) ∈ S) ∧ ∃ y, p.1 y = p.2 y}
abbrev RemoveCode {n : ℕ} (S : Finset (C × Fin n)) :=
  (y : C) × (({x // x ≠ y} → Fin n) × (C → S))
def encodeRemove {n : ℕ} (S : Finset (C × Fin n)) (p : RemoveSupportedPairs S) :
    RemoveCode S := by
  classical
  exact ⟨p.property.2.choose, (fun x => p.val.1 x),
    fun x => ⟨(x, p.val.2 x), p.property.1 x⟩⟩
def decodeRemove {n : ℕ} (S : Finset (C × Fin n)) (p : RemoveCode S) :
    (C → Fin n) × (C → Fin n) := by
  classical
  exact ⟨(fun x => if h : x = p.1 then (p.2.2 x).val.2 else p.2.1 ⟨x, h⟩),
    fun x => (p.2.2 x).val.2⟩
theorem decode_encodeRemove {n : ℕ} (S : Finset (C × Fin n)) (p : RemoveSupportedPairs S) :
    decodeRemove S (encodeRemove S p) = p.val := by
  classical
  apply Prod.ext
  · funext x
    by_cases hx : x = p.property.2.choose
    · simpa [decodeRemove, encodeRemove, hx] using p.property.2.choose_spec.symm
    · simp [decodeRemove, encodeRemove, hx]
  · rfl
theorem encodeRemove_injective {n : ℕ} (S : Finset (C × Fin n)) :
    Function.Injective (encodeRemove S) := by
  intro p q h
  apply Subtype.ext
  simpa only [decode_encodeRemove] using congrArg (decodeRemove S) h
theorem card_removeSupportedPairs_le {n : ℕ} (S : Finset (C × Fin n)) :
    Fintype.card (RemoveSupportedPairs S) ≤
      Fintype.card C * n ^ (Fintype.card C - 1) * S.card ^ Fintype.card C := by
  classical
  calc
    _ ≤ Fintype.card (RemoveCode S) := Fintype.card_le_of_injective _ (encodeRemove_injective S)
    _ = _ := by
      simp [RemoveCode, Fintype.card_sigma, Fintype.card_prod,
        Fintype.card_subtype_compl, Fintype.card_coe, Nat.mul_assoc]
/-- Actual ordered pairs of distinct overlapping embeddings active in add/remove order.
The first coordinate is the created embedding and the second the removed embedding. -/
abbrev ActiveAddPairs (incident : D → Finset C) {n : ℕ}
    (Ω : Finset (Primitive incident n)) :=
  {p : (C → Fin n) × (C → Fin n) // p.1 ≠ p.2 ∧
    ¬ Disjoint (edges incident p.2) (edges incident p.1) ∧
    Disjoint (edges incident p.1) Ω ∧ edges incident p.2 ⊆ Ω ∪ edges incident p.1}
/-- Actual ordered pairs active in remove/add order. -/
abbrev ActiveRemovePairs (incident : D → Finset C) {n : ℕ}
    (Ω : Finset (Primitive incident n)) :=
  {p : (C → Fin n) × (C → Fin n) // p.1 ≠ p.2 ∧
    ¬ Disjoint (edges incident p.2) (edges incident p.1) ∧
    edges incident p.2 ⊆ Ω ∧ Disjoint (edges incident p.1) (Ω \ edges incident p.2)}
/-- Explicit connected-component add/remove count. No row-sum bound is assumed. -/
theorem card_activeAddPairs_le (incident : D → Finset C)
    (hne : ∀ d, (incident d).Nonempty) (hincident : ∀ x, ∃ d, x ∈ incident d)
    (hconnected : CrossesEveryCut incident) {n : ℕ}
    (Ω : Finset (Primitive incident n)) :
    Fintype.card (ActiveAddPairs incident Ω) ≤
      Fintype.card C * n ^ (Fintype.card C - 1) * (support incident Ω).card *
        ((support incident Ω).card + 1) ^ Fintype.card C := by
  classical
  let f : ActiveAddPairs incident Ω → AddSupportedPairs (support incident Ω) := fun p =>
    ⟨p.val, (fun x h => changed_label_is_supported incident hincident p.val.1 p.val.2 Ω
      p.property.2.2.2 x h), by
        obtain ⟨y, _, hy⟩ := unchanged_label_is_supported incident hconnected p.val.1 p.val.2 Ω
          p.property.2.2.2 (changedRoles_nonempty_of_ne _ _ p.property.1)
          (changedRoles_ne_univ_of_not_disjoint incident hne _ _
            (by simpa only [disjoint_comm] using p.property.2.1))
        exact ⟨y, hy⟩⟩
  have hf : Function.Injective f := by
    intro p q h
    exact Subtype.ext (congrArg (fun z : AddSupportedPairs (support incident Ω) => z.val) h)
  exact (Fintype.card_le_of_injective f hf).trans (card_addSupportedPairs_le _)
/-- Explicit connected-component remove/add count. -/
theorem card_activeRemovePairs_le (incident : D → Finset C)
    (hne : ∀ d, (incident d).Nonempty) (hincident : ∀ x, ∃ d, x ∈ incident d)
    {n : ℕ} (Ω : Finset (Primitive incident n)) :
    Fintype.card (ActiveRemovePairs incident Ω) ≤
      Fintype.card C * n ^ (Fintype.card C - 1) * (support incident Ω).card ^ Fintype.card C := by
  classical
  let f : ActiveRemovePairs incident Ω → RemoveSupportedPairs (support incident Ω) := fun p =>
    ⟨p.val, (fun x => removed_label_is_supported incident hincident p.val.2 Ω
      p.property.2.2.1 x), exists_equal_of_not_disjoint incident hne p.val.1 p.val.2
        (by simpa only [disjoint_comm] using p.property.2.1)⟩
  have hf : Function.Injective f := by
    intro p q h
    exact Subtype.ext (congrArg (fun z : RemoveSupportedPairs (support incident Ω) => z.val) h)
  exact (Fintype.card_le_of_injective f hf).trans (card_removeSupportedPairs_le _)
/-- Both overlapping transition orders obey the required one-label-saving bound.
The explicit constant 2c is no larger than the report's 2^c+c. -/
theorem card_activePairs_le (incident : D → Finset C)
    (hne : ∀ d, (incident d).Nonempty) (hincident : ∀ x, ∃ d, x ∈ incident d)
    (hdegree : ∀ d, (incident d).card ≤ 2) (hconnected : CrossesEveryCut incident)
    {n : ℕ} (Ω : Finset (Primitive incident n)) :
    Fintype.card (ActiveAddPairs incident Ω) + Fintype.card (ActiveRemovePairs incident Ω) ≤
      (2 * Fintype.card C) * n ^ (Fintype.card C - 1) *
        (1 + 2 * Ω.card) ^ (Fintype.card C + 1) := by
  let c := Fintype.card C
  let m := (support incident Ω).card
  let b := 1 + 2 * Ω.card
  have hm : m + 1 ≤ b := by
    have h := card_support_le incident hdegree Ω
    dsimp [m, b]
    omega
  have hb : 1 ≤ b := by dsimp [b]; omega
  have ha := card_activeAddPairs_le incident hne hincident hconnected Ω
  have hr := card_activeRemovePairs_le incident hne hincident Ω
  have hpow : (m + 1) ^ c ≤ b ^ c := Nat.pow_le_pow_left hm c
  have hpow' : m ^ c ≤ b ^ c := Nat.pow_le_pow_left (by omega : m ≤ b) c
  have hadd : c * n ^ (c - 1) * m * (m + 1) ^ c ≤ c * n ^ (c - 1) * b ^ (c + 1) := by
    calc
      _ ≤ c * n ^ (c - 1) * b * b ^ c :=
        Nat.mul_le_mul (Nat.mul_le_mul_left _ (by omega : m ≤ b)) hpow
      _ = _ := by rw [pow_succ]; ring
  have hrem : c * n ^ (c - 1) * m ^ c ≤ c * n ^ (c - 1) * b ^ (c + 1) := by
    apply Nat.mul_le_mul_left
    calc
      _ ≤ b ^ c := hpow'
      _ ≤ b ^ c * b := Nat.le_mul_of_pos_right _ hb
      _ = _ := (pow_succ _ _).symm
  change _ ≤ (2 * c) * n ^ (c - 1) * b ^ (c + 1)
  calc
    _ ≤ c * n ^ (c - 1) * b ^ (c + 1) + c * n ^ (c - 1) * b ^ (c + 1) :=
      Nat.add_le_add (ha.trans hadd) (hr.trans hrem)
    _ = _ := by ring
end
end Colored
end GraphMatrices.OccupationCreation
