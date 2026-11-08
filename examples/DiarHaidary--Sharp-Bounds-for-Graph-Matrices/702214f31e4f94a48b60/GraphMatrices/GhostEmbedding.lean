import GraphMatrices.BoundaryAmbient

/-! Extending a partial primitive-edge injection by unused ghost coordinates.
This permits arbitrary disjoint role pools inside the actual label universe. -/

namespace GraphMatrices.GhostEmbedding

noncomputable section
attribute [local instance] Classical.propDecidable
open scoped BigOperators
open OccupationCreation OccupationCreation.Colored BoundaryCreation

variable {P E : Type*} [Fintype P] [DecidableEq P] [Fintype E] [DecidableEq E]

/-- Good primitive coordinates use their actual edge; all others receive a
distinct coordinate in a separate summand. -/
def extendEmbedding (good : P → Prop) (f : {x // good x} ↪ E) : P ↪ E ⊕ P where
  toFun x := if h : good x then Sum.inl (f ⟨x, h⟩) else Sum.inr x
  inj' := by
    intro x y h
    by_cases hx : good x <;> by_cases hy : good y
    · simp only [hx, hy, dite_true, Sum.inl.injEq] at h
      exact congrArg Subtype.val (f.injective h)
    · simp [hx, hy] at h
    · simp [hx, hy] at h
    · simpa [hx, hy] using h

@[simp] theorem extendEmbedding_good (good : P → Prop) (f : {x // good x} ↪ E)
    (x : P) (hx : good x) : extendEmbedding good f x = Sum.inl (f ⟨x, hx⟩) := by
  change (if h : good x then Sum.inl (f ⟨x, h⟩) else Sum.inr x) = _
  simp only [dif_pos hx]

def realEdges (good : P → Prop) (f : {x // good x} ↪ E) (A : Finset P) : Finset E :=
  (A.subtype good).image f

                                               
                                                                                  
                                            
                                                      
       
             
            
                                                
                                                                     
                                                                                
            
                                               
                                          
                                                                                 

theorem extendEmbedding_image (good : P → Prop) (f : {x // good x} ↪ E)
    (A : Finset P) (hA : ∀ x ∈ A, good x) :
    A.image (extendEmbedding good f) = (realEdges good f A).image Sum.inl := by
  ext z
  constructor
  · rintro hz
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 hz
    apply Finset.mem_image.2
    refine ⟨f ⟨x, hA x hx⟩, ?_, ?_⟩
    · exact Finset.mem_image.2 ⟨⟨x, hA x hx⟩, Finset.mem_subtype.2 hx, rfl⟩
    · exact (extendEmbedding_good good f x (hA x hx)).symm
  · rintro hz
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.1 hz
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 hy
    exact Finset.mem_image.2 ⟨x.val, Finset.mem_subtype.1 hx,
      extendEmbedding_good good f x.val x.property⟩

def stateEmbedding : State E ↪ State (E ⊕ P) where
  toFun Ω := Ω.image Sum.inl
  inj' := Finset.image_injective Sum.inl_injective

@[simp] theorem stateEmbedding_card (Ω : State E) :
    (stateEmbedding (P := P) Ω).card = Ω.card :=
  Finset.card_image_of_injective _ Sum.inl_injective

theorem creationAtom_real (A target source : State E) :
    creationAtom (A.image (Sum.inl : E → E ⊕ P))
      (stateEmbedding target) (stateEmbedding source) = creationAtom A target source := by
  simp only [stateEmbedding, Function.Embedding.coeFn_mk, creationAtom_apply,
    ← Finset.image_union]
  have hd : Disjoint (A.image (Sum.inl : E → E ⊕ P)) (source.image Sum.inl) ↔
      Disjoint A source := by
    rw [Finset.disjoint_left, Finset.disjoint_left]
    constructor
    · intro h x hxA hxS
      exact h (Finset.mem_image.2 ⟨x, hxA, rfl⟩) (Finset.mem_image.2 ⟨x, hxS, rfl⟩)
    · intro h z hzA hzS
      obtain ⟨x, hxA, rfl⟩ := Finset.mem_image.1 hzA
      obtain ⟨y, hyS, hyx⟩ := Finset.mem_image.1 hzS
      exact h hxA (Sum.inl_injective hyx ▸ hyS)
  simp only [hd, Finset.image_inj Sum.inl_injective]

variable {C D : Type*} [Fintype C] [DecidableEq C] [Fintype D] [DecidableEq D]

def indexEmbedding (B : Finset C) (n : ℕ) :
    AmbientIndex (E := E) B n ↪ AmbientIndex (E := E ⊕ P) B n where
  toFun x := (x.1, stateEmbedding x.2)
  inj' := by
    intro x y h
    apply Prod.ext
    · exact congrArg (fun z : AmbientIndex (E := E ⊕ P) B n => z.1) h
    exact stateEmbedding.injective
      (congrArg (fun z : AmbientIndex (E := E ⊕ P) B n => z.2) h)

def boundedIndexEmbedding (B : Finset C) (n K : ℕ) :
    {x : AmbientIndex (E := E) B n // x.2.card ≤ K} ↪
      {x : AmbientIndex (E := E ⊕ P) B n // x.2.card ≤ K} where
  toFun x := ⟨indexEmbedding B n x.val, by
    change (stateEmbedding (P := P) x.val.2).card ≤ K
    simpa only [stateEmbedding_card] using x.property⟩
  inj' := by
    intro x y h
    apply Subtype.ext
    exact (indexEmbedding B n).injective (congrArg Subtype.val h)

def realAtom (incident : D → Finset C) (S U : Finset C) {n : ℕ}
    (good : Primitive incident n → Prop) (f : {x // good x} ↪ E)
    (φ : C → Fin n) :
    Matrix (AmbientIndex (E := E) U n) (AmbientIndex (E := E) S n) ℝ :=
  fun target source =>
    if source.1 = boundaryLabels S φ ∧ target.1 = boundaryLabels U φ then
      creationAtom (realEdges good f (edges incident φ)) target.2 source.2
    else 0

/-- The actual creator on the real edge space, defined even when the partial
primitive map cannot be extended inside that space. -/
def realCreator (incident : D → Finset C) (S U : Finset C) {n : ℕ}
    (good : Primitive incident n → Prop) (f : {x // good x} ↪ E)
    (allowed : (C → Fin n) → Prop) :
    Matrix (AmbientIndex (E := E) U n) (AmbientIndex (E := E) S n) ℝ :=
  ∑ φ, if allowed φ then realAtom incident S U good f φ else 0

def boundedRealCreator (incident : D → Finset C) (S U : Finset C) {n : ℕ}
    (good : Primitive incident n → Prop) (f : {x // good x} ↪ E)
    (allowed : (C → Fin n) → Prop) (K : ℕ) :=
  (realCreator incident S U good f allowed).submatrix id
    (Subtype.val : {x : AmbientIndex (E := E) S n // x.2.card ≤ K} → _)

theorem realCreator_eq_submatrix (incident : D → Finset C) (S U : Finset C) {n : ℕ}
    (good : Primitive incident n → Prop) (f : {x // good x} ↪ E)
    (allowed : (C → Fin n) → Prop)
    (hgood : ∀ φ, allowed φ → ∀ x ∈ edges incident φ, good x) :
    realCreator incident S U good f allowed =
      (ambientCreator incident S U (extendEmbedding good f) allowed).submatrix
        (indexEmbedding U n) (indexEmbedding S n) := by
  ext target source
  simp only [realCreator, ambientCreator, Matrix.submatrix_apply, Matrix.sum_apply]
  apply Finset.sum_congr rfl
  intro φ _
  by_cases hφ : allowed φ
  · simp only [hφ, if_true, ambientAtom, realAtom]
    change (if source.1 = boundaryLabels S φ ∧ target.1 = boundaryLabels U φ then
      creationAtom (realEdges good f (edges incident φ)) target.2 source.2 else 0) =
      if source.1 = boundaryLabels S φ ∧ target.1 = boundaryLabels U φ then
        creationAtom ((edges incident φ).image (extendEmbedding good f))
          (stateEmbedding target.2) (stateEmbedding source.2) else 0
    rw [extendEmbedding_image good f _ (hgood φ hφ), creationAtom_real]
  · simp [hφ]

theorem boundedRealCreator_eq_submatrix (incident : D → Finset C) (S U : Finset C) {n : ℕ}
    (good : Primitive incident n → Prop) (f : {x // good x} ↪ E)
    (allowed : (C → Fin n) → Prop)
    (hgood : ∀ φ, allowed φ → ∀ x ∈ edges incident φ, good x) (K : ℕ) :
    boundedRealCreator incident S U good f allowed K =
      (boundedAmbientCreator incident S U (extendEmbedding good f) allowed K).submatrix
        (indexEmbedding U n) (boundedIndexEmbedding S n K) := by
  ext target source
  change realCreator incident S U good f allowed target source.val = _
  rw [realCreator_eq_submatrix incident S U good f allowed hgood]
  rfl

/-- Ghost coordinates introduce no loss in the side-creation estimate: the
actual operator is a coordinate compression of the already bounded operator. -/
theorem boundedRealCreator_norm_sq_le (G : SimpleGraph C) (S U : Finset C)
    (hmin : IsMinimumSeparator G S U S) (hnf : NoFloatingAt G S U) {n : ℕ}
    (good : Primitive (graphIncident G) n → Prop) (f : {x // good x} ↪ E)
    (allowed : (C → Fin n) → Prop)
    (hgood : ∀ φ, allowed φ → ∀ x ∈ edges (graphIncident G) φ, good x) (K : ℕ) :
    spectralNorm (boundedRealCreator (graphIncident G) S U good f allowed K) ^ 2 ≤
      (n ^ (Fintype.card C - S.card) +
        (Fintype.card C - S.card) * n ^ (Fintype.card C - S.card - 1) *
          (1 + 2 * K) ^ (Fintype.card C + 1) : ℕ) := by
  rw [boundedRealCreator_eq_submatrix _ _ _ _ _ _ hgood]
  apply le_trans (pow_le_pow_left₀ (spectralNorm_nonneg _)
    (spectralNorm_submatrix_le _ (indexEmbedding U n) (boundedIndexEmbedding S n K)) 2)
  exact ambientGraphCreator_norm_sq_le G S U hmin hnf (extendEmbedding good f) allowed K

end
end GraphMatrices.GhostEmbedding
