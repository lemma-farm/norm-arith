import Examples.DiarHaidary__Sharp_Bounds_for_Graph_Matrices.Dependencies.vad36d74d65ba.GraphMatrices.OccupationCreation
import Examples.DiarHaidary__Sharp_Bounds_for_Graph_Matrices.Dependencies.vad36d74d65ba.GraphMatrices.FloatingComponents
import Examples.DiarHaidary__Sharp_Bounds_for_Graph_Matrices.Dependencies.vad36d74d65ba.GraphMatrices.SchurBound
/-!
Literal pure-creation operators with input and output boundary registers.
All role labels are retained in primitive edges. Different roles have different
colors, so an arbitrary role assignment is a globally injective colored labeling.
-/
namespace GraphMatrices.BoundaryCreation
noncomputable section
attribute [local instance] Classical.propDecidable
open scoped BigOperators
open OccupationCreation
open OccupationCreation.Colored
variable {C D : Type*} [Fintype C] [DecidableEq C] [Fintype D] [DecidableEq D]
abbrev Labels (B : Finset C) (n : ℕ) := {x // x ∈ B} → Fin n
def boundaryLabels (B : Finset C) {n : ℕ} (φ : C → Fin n) : Labels B n :=
  fun x => φ x.val
abbrev Index (incident : D → Finset C) (B : Finset C) (n : ℕ) :=
  Labels B n × State (Primitive incident n)
abbrev AssignmentsAt (S : Finset C) {n : ℕ} (A : Labels S n) :=
  {φ : C → Fin n // boundaryLabels S φ = A}
def assignmentAtEquiv (S : Finset C) {n : ℕ} (A : Labels S n) :
    AssignmentsAt S A ≃ ({x : C // x ∉ S} → Fin n) where
  toFun φ := fun x => φ.val x.val
  invFun t := ⟨fun x => if h : x ∈ S then A ⟨x, h⟩ else t ⟨x, h⟩, by
    funext x
    simp [boundaryLabels, x.property]⟩
  left_inv φ := by
    apply Subtype.ext
    funext x
    by_cases hx : x ∈ S
    · have h := congrFun φ.property ⟨x, hx⟩
      simpa [boundaryLabels, hx] using h.symm
    · simp [hx]
  right_inv t := by
    funext x
    simp [x.property]
theorem card_assignmentsAt (S : Finset C) {n : ℕ} (A : Labels S n) :
    Fintype.card (AssignmentsAt S A) = n ^ (Fintype.card C - S.card) := by
  rw [Fintype.card_congr (assignmentAtEquiv S A), Fintype.card_fun, Fintype.card_fin]
  congr 1
  simp [Fintype.card_subtype_compl, Fintype.card_coe]
/-- A pair encoded by a fixed input assignment, all changed removed labels in
the old support, and one old creation label outside the fixed input register. -/
abbrev SupportedPairs (S : Finset C) {n : ℕ} (A : Labels S n)
    (O : Finset (C × Fin n)) :=
  {p : (C → Fin n) × (C → Fin n) //
    boundaryLabels S p.1 = A ∧
    (∀ x, p.1 x ≠ p.2 x → (x, p.2 x) ∈ O) ∧
    ∃ y : {x : C // x ∉ S}, (y.val, p.1 y.val) ∈ O}
abbrev PairCode (S : Finset C) {n : ℕ} (O : Finset (C × Fin n)) :=
  (y : {x : C // x ∉ S}) ×
    (({x : {x : C // x ∉ S} // x ≠ y} → Fin n) × O × (C → Option O))
def encodePair (S : Finset C) {n : ℕ} (A : Labels S n)
    (O : Finset (C × Fin n)) (p : SupportedPairs S A O) : PairCode S O :=
  ⟨p.property.2.2.choose, (fun x => p.val.1 x.val.val),
    ⟨(p.property.2.2.choose.val, p.val.1 p.property.2.2.choose.val), p.property.2.2.choose_spec⟩,
    fun x => if h : p.val.1 x = p.val.2 x then none
      else some ⟨(x, p.val.2 x), p.property.2.1 x h⟩⟩
def decodeFirst (S : Finset C) {n : ℕ} (A : Labels S n)
    (O : Finset (C × Fin n)) (p : PairCode S O) : C → Fin n :=
  fun x => if hx : x ∈ S then A ⟨x, hx⟩
    else if hy : (⟨x, hx⟩ : {x : C // x ∉ S}) = p.1 then p.2.2.1.val.2
      else p.2.1 ⟨⟨x, hx⟩, hy⟩
def decodePair (S : Finset C) {n : ℕ} (A : Labels S n)
    (O : Finset (C × Fin n)) (p : PairCode S O) : (C → Fin n) × (C → Fin n) :=
  ⟨decodeFirst S A O p, fun x => match p.2.2.2 x with
    | none => decodeFirst S A O p x
    | some z => z.val.2⟩
theorem decodeFirst_encodePair (S : Finset C) {n : ℕ} (A : Labels S n)
    (O : Finset (C × Fin n)) (p : SupportedPairs S A O) :
    decodeFirst S A O (encodePair S A O p) = p.val.1 := by
  funext x
  by_cases hx : x ∈ S
  · have ha := congrFun p.property.1 ⟨x, hx⟩
    simpa [decodeFirst, encodePair, boundaryLabels, hx] using ha.symm
  · by_cases hy : (⟨x, hx⟩ : {x : C // x ∉ S}) = p.property.2.2.choose
    · have hxy : x = p.property.2.2.choose.val := congrArg Subtype.val hy
      simp [decodeFirst, encodePair, hxy, p.property.2.2.choose.property]
    · simp [decodeFirst, encodePair, hx, hy]
theorem decode_encodePair (S : Finset C) {n : ℕ} (A : Labels S n)
    (O : Finset (C × Fin n)) (p : SupportedPairs S A O) :
    decodePair S A O (encodePair S A O p) = p.val := by
  apply Prod.ext
  · exact decodeFirst_encodePair S A O p
  · funext x
    change (match (encodePair S A O p).2.2.2 x with
      | none => decodeFirst S A O (encodePair S A O p) x
      | some z => z.val.2) = p.val.2 x
    rw [decodeFirst_encodePair]
    by_cases h : p.val.1 x = p.val.2 x <;> simp [encodePair, h]
theorem encodePair_injective (S : Finset C) {n : ℕ} (A : Labels S n)
    (O : Finset (C × Fin n)) : Function.Injective (encodePair S A O) := by
  intro p q h
  apply Subtype.ext
  simpa only [decode_encodePair] using congrArg (decodePair S A O) h
/-- The explicit count has one fewer free creation label than the diagonal.
The code is injective and reconstructs both complete role assignments. -/
theorem card_supportedPairs_le (S : Finset C) {n : ℕ} (A : Labels S n)
    (O : Finset (C × Fin n)) :
    Fintype.card (SupportedPairs S A O) ≤
      (Fintype.card C - S.card) * n ^ (Fintype.card C - S.card - 1) *
        O.card * (O.card + 1) ^ Fintype.card C := by
  calc
    _ ≤ Fintype.card (PairCode S O) :=
      Fintype.card_le_of_injective _ (encodePair_injective S A O)
    _ = _ := by
      simp [PairCode, Fintype.card_sigma, Fintype.card_prod, Fintype.card_fun,
        Fintype.card_subtype_compl, Fintype.card_subtype_eq, Fintype.card_coe, Nat.mul_assoc]
/-- Active distinct Gram embedding pairs at a fixed input state. -/
abbrev ActivePairs (incident : D → Finset C) (S U : Finset C) {n : ℕ}
    (A : Labels S n) (Ω : State (Primitive incident n)) :=
  {p : (C → Fin n) × (C → Fin n) // p.1 ≠ p.2 ∧
    boundaryLabels S p.1 = A ∧ boundaryLabels U p.1 = boundaryLabels U p.2 ∧
    Disjoint (edges incident p.1) Ω ∧ edges incident p.2 ⊆ Ω ∪ edges incident p.1}
theorem activePairs_support_restrictions (G : SimpleGraph C) (incident : D → Finset C)
    (S U : Finset C) (hmin : IsMinimumSeparator G S U S) (hnf : NoFloatingAt G S U)
    (hedges : ∀ x y, G.Adj x y → ∃ d, x ∈ incident d ∧ y ∈ incident d)
    {n : ℕ} (A : Labels S n) (Ω : State (Primitive incident n))
    (p : ActivePairs incident S U A Ω) :
    (∀ x, p.val.1 x ≠ p.val.2 x → (x, p.val.2 x) ∈ support incident Ω) ∧
      ∃ y : {x : C // x ∉ S}, (y.val, p.val.1 y.val) ∈ support incident Ω := by
  have hout : ∀ x ∈ U, p.val.1 x = p.val.2 x := by
    intro x hx
    exact congrFun p.property.2.2.1 ⟨x, hx⟩
  have hchanged : ∀ x ∈ changedRoles p.val.1 p.val.2, x ∉ U := by
    intro x hx hxU
    exact (mem_changedRoles _ _ x).1 hx (hout x hxU)
  constructor
  · intro x hx
    have hxU : x ∉ U := fun hxU => hx (hout x hxU)
    obtain ⟨y, hxy⟩ := nonisolated_of_side_hypotheses hmin hnf hxU
    obtain ⟨d, hxd, _⟩ := hedges x y hxy
    exact endpoint_mem_support incident Ω (primitive incident p.val.2 d)
      (changed_edge_is_occupied incident p.val.1 p.val.2 Ω p.property.2.2.2.2 d x hxd hx)
      x hxd
  · obtain ⟨x, hxT, y, hyT, hyS, hxy⟩ := changed_set_has_unchanged_neighbor hmin hnf
      (changedRoles p.val.1 p.val.2) (changedRoles_nonempty_of_ne _ _ p.property.1) hchanged
    obtain ⟨d, hxd, hyd⟩ := hedges x y hxy
    have hyEq : p.val.1 y = p.val.2 y := by simpa using hyT
    refine ⟨⟨y, hyS⟩, ?_⟩
    rw [hyEq]
    exact endpoint_mem_support incident Ω (primitive incident p.val.2 d)
      (changed_edge_is_occupied incident p.val.1 p.val.2 Ω p.property.2.2.2.2 d x hxd
        ((mem_changedRoles _ _ x).1 hxT)) y hyd
/-- The one-free-label-saving count is derived from genuine minimum-separator
and graph-component hypotheses, not assumed as a numerical certificate. -/
theorem card_activePairs_le (G : SimpleGraph C) (incident : D → Finset C)
    (S U : Finset C) (hmin : IsMinimumSeparator G S U S) (hnf : NoFloatingAt G S U)
    (hedges : ∀ x y, G.Adj x y → ∃ d, x ∈ incident d ∧ y ∈ incident d)
    {n : ℕ} (A : Labels S n) (Ω : State (Primitive incident n)) :
    Fintype.card (ActivePairs incident S U A Ω) ≤
      (Fintype.card C - S.card) * n ^ (Fintype.card C - S.card - 1) *
        (support incident Ω).card * ((support incident Ω).card + 1) ^ Fintype.card C := by
  let f : ActivePairs incident S U A Ω → SupportedPairs S A (support incident Ω) :=
    fun p => ⟨p.val, p.property.2.1, activePairs_support_restrictions G incident S U
      hmin hnf hedges A Ω p⟩
  have hf : Function.Injective f := by
    intro p q h
    exact Subtype.ext (congrArg (fun z : SupportedPairs S A (support incident Ω) => z.val) h)
  exact (Fintype.card_le_of_injective f hf).trans (card_supportedPairs_le S A _)
theorem card_activePairs_le_grade (G : SimpleGraph C) (incident : D → Finset C)
    (S U : Finset C) (hmin : IsMinimumSeparator G S U S) (hnf : NoFloatingAt G S U)
    (hedges : ∀ x y, G.Adj x y → ∃ d, x ∈ incident d ∧ y ∈ incident d)
    (hdegree : ∀ d, (incident d).card ≤ 2)
    {n : ℕ} (A : Labels S n) (Ω : State (Primitive incident n)) :
    Fintype.card (ActivePairs incident S U A Ω) ≤
      (Fintype.card C - S.card) * n ^ (Fintype.card C - S.card - 1) *
        (1 + 2 * Ω.card) ^ (Fintype.card C + 1) := by
  have hm := card_support_le incident hdegree Ω
  have hma : (support incident Ω).card + 1 ≤ 1 + 2 * Ω.card := by omega
  calc
    _ ≤ (Fintype.card C - S.card) * n ^ (Fintype.card C - S.card - 1) *
        (support incident Ω).card * ((support incident Ω).card + 1) ^ Fintype.card C :=
      card_activePairs_le G incident S U hmin hnf hedges A Ω
    _ ≤ (Fintype.card C - S.card) * n ^ (Fintype.card C - S.card - 1) *
        (1 + 2 * Ω.card) * (1 + 2 * Ω.card) ^ Fintype.card C := by
      exact Nat.mul_le_mul (Nat.mul_le_mul_left _ (by omega)) (Nat.pow_le_pow_left hma _)
    _ = _ := by rw [pow_succ]; ring
/-- The incidence data of a literal finite simple graph: every edge has its
actual two endpoints. -/
abbrev graphIncident (G : SimpleGraph C) : G.edgeSet → Finset C :=
  fun e => e.val.toFinset
theorem graphIncident_degree (G : SimpleGraph C) (d : G.edgeSet) :
    (graphIncident G d).card ≤ 2 := by
  have h : ¬ d.val.IsDiag := G.not_isDiag_of_mem_edgeSet d.property
  exact le_of_eq (Sym2.card_toFinset_of_not_isDiag d.val h)
theorem graphIncident_represents (G : SimpleGraph C) (x y : C) (hxy : G.Adj x y) :
    ∃ d : G.edgeSet, x ∈ graphIncident G d ∧ y ∈ graphIncident G d := by
  refine ⟨⟨s(x, y), hxy⟩, ?_, ?_⟩ <;> simp [graphIncident]
end
end GraphMatrices.BoundaryCreation
