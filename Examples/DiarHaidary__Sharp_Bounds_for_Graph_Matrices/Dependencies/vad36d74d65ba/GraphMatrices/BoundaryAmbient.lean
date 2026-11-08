import Examples.DiarHaidary__Sharp_Bounds_for_Graph_Matrices.Dependencies.vad36d74d65ba.GraphMatrices.BoundaryCreationNorm
/-! Side creators in an arbitrary larger primitive-edge universe. -/
namespace GraphMatrices.BoundaryCreation
noncomputable section
attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 1000000
open scoped BigOperators
open OccupationCreation
open OccupationCreation.Colored
variable {C D E : Type*} [Fintype C] [DecidableEq C] [Fintype D] [DecidableEq D]
  [Fintype E] [DecidableEq E]
abbrev AmbientIndex (B : Finset C) (n : ℕ) := Labels B n × State E
def ambientAtom (incident : D → Finset C) (S U : Finset C) {n : ℕ}
    (e : Primitive incident n ↪ E) (φ : C → Fin n) :
    Matrix (AmbientIndex (E := E) U n) (AmbientIndex (E := E) S n) ℝ :=
  fun target source =>
    if source.1 = boundaryLabels S φ ∧ target.1 = boundaryLabels U φ then
      creationAtom ((edges incident φ).image e) target.2 source.2
    else 0
def ambientCreator (incident : D → Finset C) (S U : Finset C) {n : ℕ}
    (e : Primitive incident n ↪ E) (allowed : (C → Fin n) → Prop) :
    Matrix (AmbientIndex (E := E) U n) (AmbientIndex (E := E) S n) ℝ :=
  ∑ φ : C → Fin n, if allowed φ then ambientAtom incident S U e φ else 0
theorem ambientAtom_apply (incident : D → Finset C) (S U : Finset C) {n : ℕ}
    (e : Primitive incident n ↪ E) (φ : C → Fin n)
    (target : AmbientIndex (E := E) U n) (source : AmbientIndex (E := E) S n) :
    ambientAtom incident S U e φ target source =
      if source.1 = boundaryLabels S φ ∧ target.1 = boundaryLabels U φ ∧
        Disjoint ((edges incident φ).image e) source.2 ∧
        target.2 = source.2 ∪ (edges incident φ).image e
      then 1 else 0 := by
  simp only [ambientAtom, creationAtom_apply]
  split_ifs <;> simp_all
theorem ambientAtom_gram_apply (incident : D → Finset C) (S U : Finset C) {n : ℕ}
    (e : Primitive incident n ↪ E) (φ ψ : C → Fin n)
    (target source : AmbientIndex (E := E) S n) :
    ((ambientAtom incident S U e ψ).transpose * ambientAtom incident S U e φ) target source =
      if source.1 = boundaryLabels S φ ∧ target.1 = boundaryLabels S ψ ∧
        boundaryLabels U φ = boundaryLabels U ψ ∧
        Disjoint ((edges incident φ).image e) source.2 ∧
        (edges incident ψ).image e ⊆ source.2 ∪ (edges incident φ).image e ∧
        target.2 = (source.2 ∪ (edges incident φ).image e) \ (edges incident ψ).image e
      then 1 else 0 := by
  classical
  rw [Matrix.mul_apply]
  rw [Finset.sum_eq_single
    (boundaryLabels U φ, source.2 ∪ (edges incident φ).image e)]
  · simp only [Matrix.transpose_apply, ambientAtom_apply]
    have hrel := add_remove_relation ((edges incident ψ).image e) target.2
      (source.2 ∪ (edges incident φ).image e)
    by_cases hsource : source.1 = boundaryLabels S φ
    · by_cases hdis : Disjoint ((edges incident φ).image e) source.2
      · simp only [hsource, hdis, true_and, and_true, if_true, mul_one]
        simp only [← and_assoc, hrel]
      · simp [hdis]
    · simp [hsource]
  · intro z _ hz
    have hzfalse : ¬ (z.1 = boundaryLabels U φ ∧ z.2 = source.2 ∪ (edges incident φ).image e) := by
      rintro ⟨h₁, h₂⟩
      exact hz (Prod.ext h₁ h₂)
    have hatom : ambientAtom incident S U e φ z source = 0 := by
      rw [ambientAtom_apply]
      split_ifs with h
      · exact False.elim (hzfalse ⟨h.2.1, h.2.2.2⟩)
      · rfl
    rw [hatom, mul_zero]
  · simp
theorem image_subset_union_iff (incident : D → Finset C) {n : ℕ}
    (e : Primitive incident n ↪ E) (A B : State (Primitive incident n)) (Ω : State E) :
    A.image e ⊆ Ω ∪ B.image e ↔ A ⊆ pullback e Ω ∪ B := by
  constructor
  · intro h x hx
    obtain hxΩ | hxB := Finset.mem_union.1 (h (Finset.mem_image.2 ⟨x, hx, rfl⟩))
    · exact Finset.mem_union_left _ ((mem_pullback e Ω x).2 hxΩ)
    · obtain ⟨y, hy, hyx⟩ := Finset.mem_image.1 hxB
      exact Finset.mem_union_right _ (e.injective hyx ▸ hy)
  · intro h z hz
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 hz
    obtain hxΩ | hxB := Finset.mem_union.1 (h hx)
    · exact Finset.mem_union_left _ ((mem_pullback e Ω x).1 hxΩ)
    · exact Finset.mem_union_right _ (Finset.mem_image.2 ⟨x, hxB, rfl⟩)
theorem ambientAtom_gram_column_sum (incident : D → Finset C) (S U : Finset C) {n : ℕ}
    (e : Primitive incident n ↪ E) (φ ψ : C → Fin n) (source : AmbientIndex (E := E) S n) :
    (∑ target, |((ambientAtom incident S U e ψ).transpose *
      ambientAtom incident S U e φ) target source|) =
      if pairEnabled incident S U φ ψ (source.1, pullback e source.2) then 1 else 0 := by
  classical
  have hpoint (target : AmbientIndex (E := E) S n) :
      |((ambientAtom incident S U e ψ).transpose * ambientAtom incident S U e φ) target source| =
        if pairEnabled incident S U φ ψ (source.1, pullback e source.2) then
          if target = (boundaryLabels S ψ,
            (source.2 ∪ (edges incident φ).image e) \ (edges incident ψ).image e)
          then 1 else 0
        else 0 := by
    rw [ambientAtom_gram_apply]
    simp only [image_disjoint_iff, image_subset_union_iff]
    simp only [pairEnabled, Prod.ext_iff]
    split_ifs <;> simp_all [eq_comm]
  simp_rw [hpoint]
  by_cases h : pairEnabled incident S U φ ψ (source.1, pullback e source.2) <;> simp [h]
theorem ambientCreator_gram_sum_pairs (incident : D → Finset C) (S U : Finset C) {n : ℕ}
    (e : Primitive incident n ↪ E) (allowed : (C → Fin n) → Prop) :
    (ambientCreator incident S U e allowed).transpose * ambientCreator incident S U e allowed =
      ∑ φ : C → Fin n, ∑ ψ : C → Fin n,
        if allowed φ ∧ allowed ψ then
          (ambientAtom incident S U e ψ).transpose * ambientAtom incident S U e φ else 0 := by
  unfold ambientCreator
  simp only [Matrix.transpose_sum, Matrix.sum_mul, Matrix.mul_sum]
  apply Finset.sum_congr rfl
  intro φ _
  apply Finset.sum_congr rfl
  intro ψ _
  by_cases hφ : allowed φ <;> by_cases hψ : allowed ψ <;> simp [hφ, hψ]
theorem enabled_pair_sum_le (incident : D → Finset C) (S U : Finset C) {n : ℕ}
    (source : Index incident S n) :
    (∑ φ : C → Fin n, ∑ ψ : C → Fin n,
      if pairEnabled incident S U φ ψ source then (1 : ℝ) else 0) ≤
        (n ^ (Fintype.card C - S.card) : ℕ) +
          Fintype.card (ActivePairs incident S U source.1 source.2) := by
  calc
    _ ≤ ∑ φ : C → Fin n, ∑ ψ : C → Fin n,
        ((if ψ = φ ∧ boundaryLabels S φ = source.1 then (1 : ℝ) else 0) +
          (if φ ≠ ψ ∧ pairEnabled incident S U φ ψ source then 1 else 0)) := by
      apply Finset.sum_le_sum
      intro φ _
      apply Finset.sum_le_sum
      intro ψ _
      by_cases heq : φ = ψ
      · subst ψ
        by_cases ha : boundaryLabels S φ = source.1 <;> simp [pairEnabled, ha]
        split_ifs <;> norm_num
      · simp [heq, Ne.symm heq]
    _ = _ := by
      simp only [Finset.sum_add_distrib]
      rw [← active_card_eq_sum]
      congr 1
      have hcard : (Fintype.card (AssignmentsAt S source.1) : ℝ) =
          ∑ φ : C → Fin n, if boundaryLabels S φ = source.1 then 1 else 0 := by
        simp [AssignmentsAt, Fintype.card_subtype]
      rw [← card_assignmentsAt S source.1, hcard]
      apply Finset.sum_congr rfl
      intro φ _
      by_cases ha : boundaryLabels S φ = source.1 <;> simp [ha]
theorem ambientCreator_gram_column_sum_le (incident : D → Finset C) (S U : Finset C) {n : ℕ}
    (e : Primitive incident n ↪ E) (allowed : (C → Fin n) → Prop)
    (source : AmbientIndex (E := E) S n) :
    (∑ target, |((ambientCreator incident S U e allowed).transpose *
      ambientCreator incident S U e allowed) target source|) ≤
        (n ^ (Fintype.card C - S.card) : ℕ) +
          Fintype.card (ActivePairs incident S U source.1 (pullback e source.2)) := by
  rw [ambientCreator_gram_sum_pairs]
  simp only [Matrix.sum_apply]
  calc
    _ ≤ ∑ target, ∑ φ : C → Fin n, ∑ ψ : C → Fin n,
        |(if allowed φ ∧ allowed ψ then
          (ambientAtom incident S U e ψ).transpose * ambientAtom incident S U e φ else 0)
          target source| := by
      apply Finset.sum_le_sum
      intro target _
      exact (Finset.abs_sum_le_sum_abs _ _).trans
        (Finset.sum_le_sum fun φ _ => Finset.abs_sum_le_sum_abs _ _)
    _ ≤ ∑ target, ∑ φ : C → Fin n, ∑ ψ : C → Fin n,
        |((ambientAtom incident S U e ψ).transpose * ambientAtom incident S U e φ) target source| := by
      apply Finset.sum_le_sum
      intro target _
      apply Finset.sum_le_sum
      intro φ _
      apply Finset.sum_le_sum
      intro ψ _
      split_ifs
      · exact le_rfl
      · simpa only [Matrix.zero_apply, abs_zero] using
          (abs_nonneg (((ambientAtom incident S U e ψ).transpose *
            ambientAtom incident S U e φ) target source))
    _ = ∑ φ : C → Fin n, ∑ ψ : C → Fin n,
        if pairEnabled incident S U φ ψ (source.1, pullback e source.2) then 1 else 0 := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro φ _
      rw [Finset.sum_comm]
      simp_rw [ambientAtom_gram_column_sum]
    _ ≤ _ := enabled_pair_sum_le incident S U (source.1, pullback e source.2)
def boundedAmbientCreator (incident : D → Finset C) (S U : Finset C) {n : ℕ}
    (e : Primitive incident n ↪ E) (allowed : (C → Fin n) → Prop) (K : ℕ) :
    Matrix (AmbientIndex (E := E) U n)
      {source : AmbientIndex (E := E) S n // source.2.card ≤ K} ℝ :=
  (ambientCreator incident S U e allowed).submatrix id Subtype.val
private theorem sum_subtype_le {α : Type*} [Fintype α] (p : α → Prop)
    [DecidablePred p] (f : α → ℝ) (hf : ∀ x, 0 ≤ f x) :
    (∑ x : {x // p x}, f x.val) ≤ ∑ x, f x := by
  calc
    _ ≤ (∑ x : {x // p x}, f x.val) + ∑ x : {x // ¬p x}, f x.val :=
      le_add_of_nonneg_right (Finset.sum_nonneg fun x _ => hf x)
    _ = _ := Fintype.sum_subtype_add_sum_subtype p f
private theorem spectralNorm_gram {m n : Type*} [Fintype m] [Fintype n]
    [DecidableEq m] [DecidableEq n] (A : Matrix m n ℝ) :
    spectralNorm (A.transpose * A) = spectralNorm A ^ 2 := by
  open scoped Matrix.Norms.L2Operator in
    simpa only [spectralNorm_eq_l2Operator, Matrix.conjTranspose_eq_transpose_of_trivial, pow_two] using
      Matrix.l2_opNorm_conjTranspose_mul_self A
/-- The side bound for arbitrary occupation states in an arbitrary larger edge
universe, and for every restricted subfamily of role assignments. In particular,
fixed disjoint pools of unequal sizes are covered. -/
theorem boundedAmbientCreator_norm_sq_le (G : SimpleGraph C) (incident : D → Finset C)
    (S U : Finset C) (hmin : IsMinimumSeparator G S U S) (hnf : NoFloatingAt G S U)
    (hedges : ∀ x y, G.Adj x y → ∃ d, x ∈ incident d ∧ y ∈ incident d)
    (hdegree : ∀ d, (incident d).card ≤ 2) {n : ℕ} (e : Primitive incident n ↪ E)
    (allowed : (C → Fin n) → Prop) (K : ℕ) :
    spectralNorm (boundedAmbientCreator incident S U e allowed K) ^ 2 ≤
      (n ^ (Fintype.card C - S.card) +
        (Fintype.card C - S.card) * n ^ (Fintype.card C - S.card - 1) *
          (1 + 2 * K) ^ (Fintype.card C + 1) : ℕ) := by
  classical
  let B : ℝ := (n ^ (Fintype.card C - S.card) +
    (Fintype.card C - S.card) * n ^ (Fintype.card C - S.card - 1) *
      (1 + 2 * K) ^ (Fintype.card C + 1) : ℕ)
  let A := boundedAmbientCreator incident S U e allowed K
  have hB : 0 ≤ B := Nat.cast_nonneg _
  have hgram (target source : {source : AmbientIndex (E := E) S n // source.2.card ≤ K}) :
      (A.transpose * A) target source =
        ((ambientCreator incident S U e allowed).transpose *
          ambientCreator incident S U e allowed) target.val source.val := by
    simp only [A, boundedAmbientCreator, Matrix.mul_apply, Matrix.transpose_apply,
      Matrix.submatrix_apply, id_eq]
  have hcols : ∀ source, ∑ target, |(A.transpose * A) target source| ≤ B := by
    intro source
    simp_rw [hgram]
    have hmass :
        (∑ target : {source : AmbientIndex (E := E) S n // source.2.card ≤ K},
          |((ambientCreator incident S U e allowed).transpose *
          ambientCreator incident S U e allowed) target.val source.val|) ≤
        (n ^ (Fintype.card C - S.card) : ℕ) +
          Fintype.card (ActivePairs incident S U source.val.1 (pullback e source.val.2)) := by
      apply le_trans ?_ (ambientCreator_gram_column_sum_le incident S U e allowed source.val)
      exact sum_subtype_le (fun target : AmbientIndex (E := E) S n => target.2.card ≤ K)
        (fun target => |((ambientCreator incident S U e allowed).transpose *
          ambientCreator incident S U e allowed) target source.val|) (fun _ => abs_nonneg _)
    apply hmass.trans
    have hcount := card_activePairs_le_grade G incident S U hmin hnf hedges hdegree
      source.val.1 (pullback e source.val.2)
    have hgrade : 1 + 2 * (pullback e source.val.2).card ≤ 1 + 2 * K := by
      have hlocal := card_pullback_le e source.val.2
      have hglobal := source.property
      omega
    have hcount' := hcount.trans (Nat.mul_le_mul_left
      ((Fintype.card C - S.card) * n ^ (Fintype.card C - S.card - 1))
      (Nat.pow_le_pow_left hgrade (Fintype.card C + 1)))
    dsimp [B]
    exact_mod_cast Nat.add_le_add_left hcount' (n ^ (Fintype.card C - S.card))
  have hrows : ∀ target, ∑ source, |(A.transpose * A) target source| ≤ B := by
    intro target
    have hsym : (A.transpose * A).transpose = A.transpose * A := by
      simp only [Matrix.transpose_mul, Matrix.transpose_transpose]
    calc
      _ = ∑ source, |(A.transpose * A) source target| := by
        apply Finset.sum_congr rfl
        intro source _
        exact congrArg abs (congrArg (fun M => M source target) hsym)
      _ ≤ B := hcols target
  have hschur := spectralNorm_schur (A.transpose * A) hB hB hrows hcols
  rw [spectralNorm_gram, Real.sqrt_mul_self hB] at hschur
  exact hschur
theorem ambientGraphCreator_norm_sq_le (G : SimpleGraph C) (S U : Finset C)
    (hmin : IsMinimumSeparator G S U S) (hnf : NoFloatingAt G S U) {n : ℕ}
    (e : Primitive (graphIncident G) n ↪ E) (allowed : (C → Fin n) → Prop) (K : ℕ) :
    spectralNorm (boundedAmbientCreator (graphIncident G) S U e allowed K) ^ 2 ≤
      (n ^ (Fintype.card C - S.card) +
        (Fintype.card C - S.card) * n ^ (Fintype.card C - S.card - 1) *
          (1 + 2 * K) ^ (Fintype.card C + 1) : ℕ) :=
  boundedAmbientCreator_norm_sq_le G (graphIncident G) S U hmin hnf
    (graphIncident_represents G) (graphIncident_degree G) e allowed K
end
end GraphMatrices.BoundaryCreation
