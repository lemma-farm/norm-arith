module

public import Mathlib

-- ==== Examples.pmaronow__ccv_palomar.Dependencies.v22907e73e11a.NearlyMinimax.HistoryShapes ====
public section
@[expose] public section
/-!
# Finite history shapes and well-defined local state updates

Shapes are quotients of finite piece words by exchanges of consecutive
independent pieces. The state obtained by applying the marked updates descends
to this quotient. Commutativity of disjoint pointwise-affine patch updates and
separate response-coordinate updates is proved concretely.
-/
noncomputable section
namespace NearlyMinimax
inductive IndependentHistoryExchange {α : Type*} (independent : α → α → Prop) : List α → List α → Prop
  | swap (before after : List α) (x y : α) (hxy : independent x y) :
      IndependentHistoryExchange independent (before ++ x :: y :: after) (before ++ y :: x :: after)
def historyShapeSetoid {α : Type*} (independent : α → α → Prop) : Setoid (List α) where
  r := Relation.EqvGen (IndependentHistoryExchange independent)
  iseqv := ⟨Relation.EqvGen.refl, fun h => Relation.EqvGen.symm _ _ h,
    fun h₁ h₂ => Relation.EqvGen.trans _ _ _ h₁ h₂⟩
def HistoryShape {α : Type*} (independent : α → α → Prop) := Quotient (historyShapeSetoid independent)

end NearlyMinimax

end
end
end

-- ==== Examples.pmaronow__ccv_palomar.Dependencies.v22907e73e11a.NearlyMinimax.HistoryShapeCount ====
public section
@[expose] public section
/-!
# Actual shape multiplicities and finite pair-chain coding

For fixed label multiplicities, a shape injects into one fixed-length binary
chain for each unordered distinct dependent pair. Its cardinality is therefore
at most the product of the pair-interleaving bounds used in the paper.
-/
noncomputable section
namespace NearlyMinimax
variable {J : Type*} [DecidableEq J]
set_option linter.unusedVariables false in
axiom _root_.NearlyMinimax.historyWord_count_shape_invariant.{w_u_1} : ∀ {J : Type w_u_1} [inst : DecidableEq J] (independent : J → J → Prop) (j : J) {u v : List J},
  Relation.EqvGen (NearlyMinimax.IndependentHistoryExchange independent) u v →
    List.count j u = List.count j v
def historyShapeMultiplicity (dependent : J → J → Prop) (j : J) :
    HistoryShape (fun a b => ¬ dependent a b) → ℕ :=
  Quotient.lift (List.count j) (fun _ _ h => historyWord_count_shape_invariant _ j h)

end NearlyMinimax

end
end
end

-- ==== Examples.pmaronow__ccv_palomar.Dependencies.v22907e73e11a.NearlyMinimax.HistoryPolynomial ====
public section
@[expose] public section
/-!
# The actual finite heap deletion polynomial

For a finite partially ordered history, coefficients enumerate all successive
deletions of maximal pieces, with their signed mark weights. Dividing the
degree-k coefficient by k! is the combinatorial order-volume coefficient.
The derivative identity is proved from this enumeration, without assuming
a transport recurrence.
-/
noncomputable section
namespace NearlyMinimax
variable {α : Type*} [PartialOrder α] [DecidableEq α]
def historyMaximalPieces (S : Finset α) : Finset α := by
  classical
  exact S.filter (fun x => ∀ y ∈ S, x ≤ y → y = x)

def historyDeletionCoefficient (weight : α → ℝ) : ℕ → Finset α → ℝ
  | 0, _ => 1
  | k + 1, S => ∑ x ∈ historyMaximalPieces S, weight x * historyDeletionCoefficient weight k (S.erase x)

end NearlyMinimax

end
end
end

-- ==== Examples.pmaronow__ccv_palomar.Dependencies.v22907e73e11a.NearlyMinimax.WordHeap ====
public section
@[expose] public section
/-!
# The actual dependency partial order of a finite history word

Pieces are occurrences in the word. Earlier dependent occurrences generate
the heap order. Antisymmetry is proved using their positions. In particular,
dependent labels are comparable, maximal pieces have distinct labels, and
the cover graph has at most one upper and one lower cover of each dependent
label. These are the combinatorial facts used in `lower_heaps`.
-/
noncomputable section
namespace NearlyMinimax
structure WordHeapPiece {J : Type*} (word : List J) (dependent : J → J → Prop) where
  position : Fin word.length
set_option linter.unusedVariables false in
axiom _root_.NearlyMinimax.WordHeapPiece.ext.{w_u_1} : ∀ {J : Type w_u_1} {word : List J} {dependent : J → J → Prop}
  {x y : NearlyMinimax.WordHeapPiece word dependent}, x.position = y.position → x = y
instance wordHeapPiece_decidableEq {J : Type*} (word : List J) (dependent : J → J → Prop) :
    DecidableEq (WordHeapPiece word dependent) := Classical.decEq _
instance wordHeapPiece_fintype {J : Type*} (word : List J) (dependent : J → J → Prop) :
    Fintype (WordHeapPiece word dependent) :=
  Fintype.ofEquiv (Fin word.length) {
    toFun := fun i => ⟨i⟩
    invFun := WordHeapPiece.position
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl }
def wordHeapLabel {J : Type*} {word : List J} {dependent : J → J → Prop}
    (x : WordHeapPiece word dependent) : J := word.get x.position
def wordHeapStep {J : Type*} {word : List J} {dependent : J → J → Prop}
    (x y : WordHeapPiece word dependent) : Prop :=
  x.position < y.position ∧ dependent (wordHeapLabel x) (wordHeapLabel y)
set_option linter.unusedVariables false in
axiom _root_.NearlyMinimax.wordHeap_reachable_position_le.{w_u_1} : ∀ {J : Type w_u_1} {word : List J} {dependent : J → J → Prop}
  {x y : NearlyMinimax.WordHeapPiece word dependent},
  Relation.ReflTransGen NearlyMinimax.wordHeapStep x y → x.position ≤ y.position
instance wordHeap_partialOrder {J : Type*} (word : List J) (dependent : J → J → Prop) :
    PartialOrder (WordHeapPiece word dependent) where
  le := Relation.ReflTransGen wordHeapStep
  le_refl _ := Relation.ReflTransGen.refl
  le_trans _ _ _ := Relation.ReflTransGen.trans
  le_antisymm x y hxy hyx := by
    apply WordHeapPiece.ext
    exact le_antisymm (wordHeap_reachable_position_le hxy) (wordHeap_reachable_position_le hyx)

def dependentLabelFinset {J : Type*} [Fintype J] (dependent : J → J → Prop) (j : J) : Finset J := by
  classical
  exact Finset.univ.filter (fun i => dependent j i)

end NearlyMinimax

end
end
end

-- ==== Examples.pmaronow__ccv_palomar.Dependencies.v22907e73e11a.NearlyMinimax.HistoryOrderVolume ====
public section
@[expose] public section
/-!
# Combinatorial order volumes of finite heap pieces

The normalized maximal-deletion count is the combinatorial order-volume
coefficient. This module proves its finite recursion, positivity bounds, and
factorization across disjoint incomparable parts. The Lebesgue chamber
identification with the paper's geometric definition is a separate bridge.
-/
noncomputable section
namespace NearlyMinimax
variable {α : Type*} [PartialOrder α] [DecidableEq α]

def historyOrderCount (S : Finset α) : ℝ := historyDeletionCoefficient (fun _ : α => (1 : ℝ)) S.card S
def historyOrderVolume (S : Finset α) : ℝ := historyOrderCount S / (S.card.factorial : ℝ)

end NearlyMinimax

end
end
end

-- ==== Examples.pmaronow__ccv_palomar.Dependencies.v22907e73e11a.NearlyMinimax.HistoryUpperSets ====
public section
@[expose] public section
/-!
# Upper subsets of a finite history

The actual finite upper-subset sum uses the combinatorial order-volume
coefficients from `HistoryOrderVolume`. Maximal deletion is reindexed by a
proved insertion/erasure bijection. No density derivative is assumed.
-/
noncomputable section
namespace NearlyMinimax
variable {α : Type*} [PartialOrder α] [DecidableEq α]
def IsHistoryUpper (S U : Finset α) : Prop :=
  U ⊆ S ∧ ∀ x ∈ U, ∀ y ∈ S, x ≤ y → y ∈ U
def historyUpperSets (S : Finset α) : Finset (Finset α) := by
  classical
  exact S.powerset.filter (IsHistoryUpper S)

def historyUpperDensity (weight : α → ℝ) (S : Finset α) (t : ℝ) : ℝ :=
  ∑ U ∈ historyUpperSets S, t ^ U.card * historyOrderVolume U * ∏ x ∈ U, weight x

def historyScaledUpperDensity (weight : α → ℝ) (ρ : ℝ) (S : Finset α) (t : ℝ) : ℝ :=
  historyUpperDensity (fun x => weight x / ρ) S t

end NearlyMinimax

end
end
end

-- ==== Examples.pmaronow__ccv_palomar.Dependencies.v22907e73e11a.NearlyMinimax.HistoryReferenceSum ====
public section
@[expose] public section
/-!
# Finite mass of the actual infinite history-shape reference law

The shape weight is `rho^length`, with the exact source
`rho = (1/2)^(Delta+1)`. Fixed-multiplicity fibers use the proved actual shape
count. Every finite shape sum is bounded by a product of finite geometric
sums, giving summability and the source normalizer bound `(4/3)^|labels|`.
-/
noncomputable section
namespace NearlyMinimax
variable {J : Type*} [Fintype J] [LinearOrder J]

def historyShapeLength (dependent : J → J → Prop)
    (g : HistoryShape (fun a b => ¬ dependent a b)) : ℕ := ∑ j : J, historyShapeMultiplicity dependent j g

def historyReferenceRho (Δ : ℕ) : ℝ := (1 / 2 : ℝ) ^ (Δ + 1)

def historyShapeReferenceWeight (dependent : J → J → Prop) (Δ : ℕ)
    (g : HistoryShape (fun a b => ¬ dependent a b)) : ℝ :=
  historyReferenceRho Δ ^ historyShapeLength dependent g

end NearlyMinimax

end
end
end

-- ==== Examples.pmaronow__ccv_palomar.Dependencies.v22907e73e11a.NearlyMinimax.HistoryReferenceMeasure ====
public section
@[expose] public section
/-!
# Actual marked-history reference probability measure

The countable shape law uses the source weight `rho^length`. Conditional on a
shape, all of its marks have the independent finite product law. The source
shape-count argument proves finiteness, and the empty shape proves nonzero
mass, so normalization constructs a probability measure without a finiteness
or positivity assumption on the desired law.
-/
noncomputable section
open MeasureTheory
namespace NearlyMinimax
variable {J : Type*} [Fintype J] [LinearOrder J]

abbrev HistoryMarked (dependent : J → J → Prop) (E : Type*) :=
  Σ g : HistoryShape (fun a b => ¬ dependent a b), Fin (historyShapeLength dependent g) → E

set_option linter.unusedVariables false in
axiom _root_.NearlyMinimax.historyShapeLength_out.{w_u_1} : ∀ {J : Type w_u_1} [inst : Fintype J] [inst_1 : LinearOrder J] (dependent : J → J → Prop)
  (g : NearlyMinimax.HistoryShape fun (a b : J) ↦ ¬dependent a b),
  NearlyMinimax.historyShapeLength dependent g = (Quotient.out g).length

/-- The unnormalized source measure: countably many shapes, independently marked. -/
def historyMarkedReferenceRaw (dependent : J → J → Prop) (Δ : ℕ) {E : Type*}
    [MeasurableSpace E] (π : Measure E) : Measure (HistoryMarked dependent E) :=
  Measure.sum fun g => ENNReal.ofReal (historyShapeReferenceWeight dependent Δ g) •
    Measure.map (Sigma.mk g) (Measure.pi fun _ : Fin (historyShapeLength dependent g) => π)

/-- The normalized actual infinite marked-history reference law `tau_0`. -/
def historyMarkedReference (dependent : J → J → Prop) (Δ : ℕ) {E : Type*}
    [MeasurableSpace E] (π : Measure E) : Measure (HistoryMarked dependent E) :=
  (historyMarkedReferenceRaw dependent Δ π Set.univ)⁻¹ • historyMarkedReferenceRaw dependent Δ π

end NearlyMinimax

end
end
end

-- ==== Examples.pmaronow__ccv_palomar.Dependencies.v22907e73e11a.NearlyMinimax.HistoryAppend ====
public section
@[expose] public section
/-!
# Actual shape append and its reference-weight change

Appending a fixed label descends through independent exchanges, is injective
by the proved dependent-pair characterization, increases length by exactly one,
and multiplies the exact source reference weight by `rho`.
-/
noncomputable section
namespace NearlyMinimax
variable {J : Type*} [Fintype J] [LinearOrder J]
omit [Fintype J] [LinearOrder J] in
set_option linter.unusedVariables false in
axiom _root_.NearlyMinimax.historyShapeRelation_append.{w_u_1} : ∀ {J : Type w_u_1} {independent : J → J → Prop} {u v : List J},
  Relation.EqvGen (NearlyMinimax.IndependentHistoryExchange independent) u v →
    ∀ (suffix : List J),
      Relation.EqvGen (NearlyMinimax.IndependentHistoryExchange independent) (u ++ suffix)
        (v ++ suffix)
/-- Appending an actual local-update label is well-defined on the history shape. -/
def historyShapeAppend (dependent : J → J → Prop) (j : J) :
    HistoryShape (fun a b => ¬ dependent a b) → HistoryShape (fun a b => ¬ dependent a b) :=
  Quotient.lift (fun word => Quotient.mk _ (word ++ [j]))
    (fun _ _ h => Quotient.sound (historyShapeRelation_append h [j]))

end NearlyMinimax

end
end
end

-- ==== Examples.pmaronow__ccv_palomar.Dependencies.v22907e73e11a.NearlyMinimax.HistoryPriorDensity ====
public section
@[expose] public section
/-!
# The actual positive polynomial density on independently marked histories

Each history is evaluated in its canonical word. Its signed weight is the
proved finite upper-set polynomial, not a prescribed prior density.
-/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory
open scoped ENNReal
namespace NearlyMinimax
variable {J : Type*} [Fintype J] [LinearOrder J]
/-- The signed mark at an actual canonical heap occurrence. -/
def historyMarkedPieceWeight (dependent : J → J → Prop) {E : Type*}
    (a : E → ℝ) (h : HistoryMarked dependent E) (x : WordHeapPiece h.1.out dependent) : ℝ :=
  a (h.2 (Fin.cast (historyShapeLength_out dependent h.1).symm x.position))
/-- The source upper-set polynomial on the actual marked dependency heap. -/
def historyMarkedDensity (dependent : J → J → Prop) (ρ t : ℝ) {E : Type*}
    (a : E → ℝ) (h : HistoryMarked dependent E) : ℝ :=
  historyScaledUpperDensity (historyMarkedPieceWeight dependent a h) ρ Finset.univ t

/-- The actual polynomial tilts the independent marks within a shape. -/
def historyMarkedFiberPrior (dependent : J → J → Prop) (Δ : ℕ) (t : ℝ) {E : Type*}
    [MeasurableSpace E] (π : Measure E) (a : E → ℝ)
    (g : HistoryShape (fun i j => ¬ dependent i j)) :
    Measure (Fin (historyShapeLength dependent g) → E) :=
  (Measure.pi (fun _ => π)).withDensity
    (fun marks => ENNReal.ofReal (historyMarkedDensity dependent (historyReferenceRho Δ) t a ⟨g, marks⟩))

/-- The actual positive marked-history prior before source reference normalization. -/
def historyMarkedPriorRaw (dependent : J → J → Prop) (Δ : ℕ) (t : ℝ) {E : Type*}
    [MeasurableSpace E] (π : Measure E) (a : E → ℝ) : Measure (HistoryMarked dependent E) :=
  Measure.sum fun g => ENNReal.ofReal (historyShapeReferenceWeight dependent Δ g) •
    Measure.map (Sigma.mk g) (historyMarkedFiberPrior dependent Δ t π a g)
/-- The path uses exactly the same time-independent source normalizer. -/
def historyMarkedPrior (dependent : J → J → Prop) (Δ : ℕ) (t : ℝ) {E : Type*}
    [MeasurableSpace E] (π : Measure E) (a : E → ℝ) : Measure (HistoryMarked dependent E) :=
  (historyMarkedReferenceRaw dependent Δ π Set.univ)⁻¹ • historyMarkedPriorRaw dependent Δ t π a

end NearlyMinimax

end
end
end

-- ==== Examples.pmaronow__ccv_palomar.Dependencies.v22907e73e11a.NearlyMinimax.HistoryCoordinateTransport ====
public section
@[expose] public section
/-!
# True finite mark-law and density transport through heap coordinates
-/
noncomputable section
open MeasureTheory
open scoped ENNReal
namespace NearlyMinimax
variable {J : Type*}
/-- Actual word occurrences and their mark coordinates. -/
def wordHeapPiecePositionEquiv (word : List J) (dependent : J → J → Prop) :
    WordHeapPiece word dependent ≃ Fin word.length where
  toFun := WordHeapPiece.position
  invFun i := ⟨i⟩
  left_inv x := by cases x; rfl
  right_inv _ := rfl
/-- A true heap isomorphism induces a bijection of actual mark coordinates. -/
def historyHeapCoordinateEquiv {u v : List J} {dependent : J → J → Prop}
    (e : WordHeapPiece u dependent ≃o WordHeapPiece v dependent) : Fin u.length ≃ Fin v.length :=
  (wordHeapPiecePositionEquiv u dependent).symm.trans
    (e.toEquiv.trans (wordHeapPiecePositionEquiv v dependent))

end NearlyMinimax

end
end
end

-- ==== Examples.pmaronow__ccv_palomar.Dependencies.v22907e73e11a.NearlyMinimax.HistoryMarkedAppend ====
public section
@[expose] public section
/-!
# Actual independent mark insertion and canonical append coordinates
-/
noncomputable section
open MeasureTheory
namespace NearlyMinimax
variable {J : Type*} [Fintype J] [LinearOrder J]
omit [Fintype J] [LinearOrder J] in
set_option linter.unusedVariables false in
axiom _root_.NearlyMinimax.historyCanonicalAppendHeapIso_exists.{w_u_1} : ∀ {J : Type w_u_1} (dependent : J → J → Prop),
  (∀ ⦃i j : J⦄, dependent i j → dependent j i) →
    ∀ (j : J) (g : NearlyMinimax.HistoryShape fun (a b : J) ↦ ¬dependent a b),
      ∃ (e :
        NearlyMinimax.WordHeapPiece (Quotient.out g ++ [j]) dependent ≃o
          NearlyMinimax.WordHeapPiece
            (Quotient.out (NearlyMinimax.historyShapeAppend dependent j g)) dependent),
        ∀ (x : NearlyMinimax.WordHeapPiece (Quotient.out g ++ [j]) dependent),
          NearlyMinimax.wordHeapLabel
              ((e :
                  NearlyMinimax.WordHeapPiece (Quotient.out g ++ [j]) dependent →
                    NearlyMinimax.WordHeapPiece
                      (Quotient.out (NearlyMinimax.historyShapeAppend dependent j g)) dependent)
                x) =
            NearlyMinimax.wordHeapLabel x
/-- Choose once an actual representative coordinate transport, not a law or score bound. -/
def historyCanonicalAppendHeapIso (dependent : J → J → Prop)
    (hsymm : ∀ ⦃i j⦄, dependent i j → dependent j i)
    (j : J) (g : HistoryShape (fun a b => ¬ dependent a b)) :
    WordHeapPiece (g.out ++ [j]) dependent ≃o
      WordHeapPiece (historyShapeAppend dependent j g).out dependent :=
  (historyCanonicalAppendHeapIso_exists dependent hsymm j g).choose

/-- Insert one genuinely independent mark at the last finite coordinate. -/
def historyFiniteMarkAppendEquiv (n : ℕ) {E : Type*} [MeasurableSpace E] :
    E × (Fin n → E) ≃ᵐ (Fin (n + 1) → E) :=
  (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => E) (Fin.last n)).symm

/-- The real position bijection from old coordinates plus a fresh last coordinate to the canonical append. -/
def historyCanonicalAppendCoordinates (dependent : J → J → Prop)
    (hsymm : ∀ ⦃i j⦄, dependent i j → dependent j i)
    (j : J) (g : HistoryShape (fun a b => ¬ dependent a b)) :
    Fin (historyShapeLength dependent g + 1) ≃ Fin (historyShapeLength dependent (historyShapeAppend dependent j g)) :=
  (finCongr (by rw [historyShapeLength_out]; simp)).trans
    ((historyHeapCoordinateEquiv (historyCanonicalAppendHeapIso dependent hsymm j g)).trans
      (finCongr (historyShapeLength_out dependent (historyShapeAppend dependent j g)).symm))
/-- Actual independent insertion followed by the actual canonical heap-coordinate permutation. -/
def historyCanonicalMarkAppendEquiv (dependent : J → J → Prop)
    (hsymm : ∀ ⦃i j⦄, dependent i j → dependent j i)
    (j : J) (g : HistoryShape (fun a b => ¬ dependent a b)) {E : Type*} [MeasurableSpace E] :
    E × (Fin (historyShapeLength dependent g) → E) ≃ᵐ
      (Fin (historyShapeLength dependent (historyShapeAppend dependent j g)) → E) :=
  (historyFiniteMarkAppendEquiv (historyShapeLength dependent g)).trans
    (MeasurableEquiv.piCongrLeft (fun _ => E) (historyCanonicalAppendCoordinates dependent hsymm j g))

end NearlyMinimax

end
end
end

-- ==== Examples.pmaronow__ccv_palomar.Dependencies.v22907e73e11a.NearlyMinimax.HistoryAppendMeasurable ====
public section
@[expose] public section
/-!
# Joint measurability of the actual marked-history append operation
-/
noncomputable section
open MeasureTheory
namespace NearlyMinimax

variable {J : Type*} [Fintype J] [LinearOrder J]
/-- Apply one independent marked local update and reorder into the genuine canonical append. -/
def historyMarkedAppend (dependent : J → J → Prop)
    (hsymm : ∀ ⦃i j⦄, dependent i j → dependent j i)
    (j : J) {E : Type*} [MeasurableSpace E] (h : HistoryMarked dependent E × E) :
    HistoryMarked dependent E :=
  ⟨historyShapeAppend dependent j h.1.1,
    historyCanonicalMarkAppendEquiv dependent hsymm j h.1.1 (h.2, h.1.2)⟩

end NearlyMinimax

end
end
end

-- ==== Examples.pmaronow__ccv_palomar.Dependencies.v22907e73e11a.NearlyMinimax.HistoryDensityDerivative ====
public section
@[expose] public section
/-!
# Genuine uniform derivative bound for the marked-history density
-/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory
namespace NearlyMinimax
variable {J : Type*} [Fintype J] [LinearOrder J]

/-- The true finite maximal-deletion expression for the time derivative. -/
def historyMarkedDensityDerivative (dependent : J → J → Prop) (ρ t : ℝ)
    {E : Type*} (a : E → ℝ) (h : HistoryMarked dependent E) : ℝ :=
  ρ⁻¹ * ∑ x ∈ historyMaximalPieces Finset.univ,
    historyMarkedPieceWeight dependent a h x *
      historyScaledUpperDensity (historyMarkedPieceWeight dependent a h) ρ (Finset.univ.erase x) t

end NearlyMinimax

end
end
end

-- ==== Examples.pmaronow__ccv_palomar.Dependencies.v22907e73e11a.NearlyMinimax.HistoryExpectationDerivative ====
public section
@[expose] public section
/-!
# Differentiating actual marked-history expectations
-/
noncomputable section
open MeasureTheory Filter Set
namespace NearlyMinimax
variable {J : Type*} [Fintype J] [LinearOrder J]
/-- The expectation weighted by the actual source history polynomial. -/
def historyMarkedExpectation (dependent : J → J → Prop) (ρ : ℝ)
    {E : Type*} [MeasurableSpace E] (μ : Measure (HistoryMarked dependent E))
    (a : E → ℝ) (F : HistoryMarked dependent E → ℝ) (t : ℝ) : ℝ :=
  ∫ h, F h * historyMarkedDensity dependent ρ t a h ∂μ

end NearlyMinimax

end
end
end

-- ==== Examples.pmaronow__ccv_palomar.Dependencies.v22907e73e11a.NearlyMinimax.HistoryWeakTransport ====
public section
@[expose] public section
/-!
# Actual weak transport of the positive marked-history prior
-/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory Filter Set
open scoped ENNReal
namespace NearlyMinimax
variable {J : Type*} [Fintype J] [LinearOrder J]
/-- The actual generator before folding the history into raw fields: append a fresh local mark. -/
def historyMarkedGeneratorExpectation (dependent : J → J → Prop)
    (hsymm : ∀ ⦃i j⦄, dependent i j → dependent j i) (ρ t : ℝ)
    {E : Type*} [MeasurableSpace E] (μ : Measure (HistoryMarked dependent E)) (π : Measure E)
    (a : E → ℝ) (F : HistoryMarked dependent E → ℝ) : ℝ :=
  ∑ j, ∫ p : HistoryMarked dependent E × E,
    F (historyMarkedAppend dependent hsymm j p) * a p.2 *
      historyMarkedDensity dependent ρ t a p.1 ∂μ.prod π

end NearlyMinimax

end
end
end

-- ==== Examples.pmaronow__ccv_palomar.Dependencies.v22907e73e11a.NearlyMinimax.HistoryPriorWeakTransport ====
public section
@[expose] public section
/-!
# Weak evolution under the actual positive history prior, rather than only its polynomial
-/
noncomputable section
open MeasureTheory Filter Set
namespace NearlyMinimax
variable {J : Type*} [Fintype J] [LinearOrder J]

/-- The signed local append expression evaluated under the actual positive prior. -/
def historyMarkedPriorGenerator (dependent : J → J → Prop)
    (hsymm : ∀ ⦃i j⦄, dependent i j → dependent j i) (Δ : ℕ) (t : ℝ)
    {E : Type*} [MeasurableSpace E] (π : Measure E) (a : E → ℝ)
    (F : HistoryMarked dependent E → ℝ) : ℝ :=
  ∑ j, ∫ p : HistoryMarked dependent E × E,
    F (historyMarkedAppend dependent hsymm j p) * a p.2
      ∂(historyMarkedPrior dependent Δ t π a).prod π

end NearlyMinimax

end
end
end

-- ==== Examples.pmaronow__ccv_palomar.Examples.Example_91413b90bb1ce9bc6dee_HighObservableProductRule ====
@[expose] public section
/-! Actual time-dependent observable product rule under the constructed history prior. -/
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
namespace NearlyMinimax
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
variable {J : Type*} [Fintype J] [LinearOrder J]
set_option linter.unusedVariables false in
/-- Differentiation of a time-dependent bounded observable under the actual
positive marked-history law. The prior derivative is proved from its genuine
source polynomial and append generator. -/
theorem historyMarkedPrior_observable_product_rule (dependent : J → J → Prop)
    (hrefl : ∀ j, dependent j j) (hsymm : ∀ ⦃i j⦄, dependent i j → dependent j i)
    (Δ : ℕ) (hΔ : 1 ≤ Δ) (hlabels : ∀ j, (dependentLabelFinset dependent j).card ≤ Δ)
    (T B t : ℝ) (ht : 0 < t) (htT : t < T) (hB : 0 ≤ B)
    {E : Type*} [MeasurableSpace E] [StandardBorelSpace E]
    (π : Measure E) [IsProbabilityMeasure π] (a : E → ℝ) (ha : Measurable a)
    (habound : ∀ e, |a e| ≤ B)
    (hsmall : T * B / historyReferenceRho Δ ≤ 1 / (2 + 8 * (Δ : ℝ) ^ 2))
    (G G' : ℝ → HistoryMarked dependent E → ℝ)
    (hGM : ∀ u, Measurable (G u)) (hG'M : ∀ u, Measurable (G' u))
    (M M' : ℝ) (hM : 0 ≤ M) (hM' : 0 ≤ M')
    (hGb : ∀ u ∈ Ioo 0 T, ∀ h, |G u h| ≤ M)
    (hG'b : ∀ u ∈ Ioo 0 T, ∀ h, |G' u h| ≤ M')
    (hGD : ∀ h u, u ∈ Ioo 0 T → HasDerivAt (fun v => G v h) (G' u h) u) 
    (h_NearlyMinimax_historyReferenceRho_pos : ∀ (Δ : ℕ), 0 < NearlyMinimax.historyReferenceRho Δ)
    (h_NearlyMinimax_historyMarkedReference_probability : ∀ {J : Type u_1} [inst : Fintype J] [inst_1 : LinearOrder J] (dependent : J → J → Prop),
      (∀ (j : J), dependent j j) →
        (∀ ⦃i j : J⦄, dependent i j → dependent j i) →
          ∀ (Δ : ℕ),
            1 ≤ Δ →
              (∀ (j : J), (NearlyMinimax.dependentLabelFinset dependent j).card ≤ Δ) →
                ∀ {E : Type u_2} [inst_2 : MeasurableSpace E] (π : MeasureTheory.Measure E)
                  [MeasureTheory.IsProbabilityMeasure π],
                  MeasureTheory.IsProbabilityMeasure
                    (NearlyMinimax.historyMarkedReference dependent Δ π))
    (h_NearlyMinimax_historyMarkedDensity_bounds : ∀ {J : Type u_1} [inst : Fintype J] [inst_1 : LinearOrder J] (dependent : J → J → Prop),
      (∀ (j : J), dependent j j) →
        (∀ ⦃i j : J⦄, dependent i j → dependent j i) →
          ∀ (Δ : ℕ),
            (∀ (j : J), (NearlyMinimax.dependentLabelFinset dependent j).card ≤ Δ) →
              ∀ (ρ t B : ℝ),
                0 < ρ →
                  0 ≤ t →
                    0 ≤ B →
                      ∀ {E : Type u_2} (a : E → ℝ),
                        (∀ (e : E), |a e| ≤ B) →
                          t * B / ρ ≤ 1 / (2 + 8 * (↑Δ : ℝ) ^ 2) →
                            ∀ (h : NearlyMinimax.HistoryMarked dependent E),
                              (1 / 2) ^ Fintype.card J ≤
                                  NearlyMinimax.historyMarkedDensity dependent ρ t a h ∧
                                NearlyMinimax.historyMarkedDensity dependent ρ t a h ≤
                                  (3 / 2) ^ Fintype.card J)
    (h_NearlyMinimax_historyMarkedPrior_integral_eq_expectation : ∀ {J : Type u_1} [inst : Fintype J] [inst_1 : LinearOrder J] (dependent : J → J → Prop),
      (∀ (j : J), dependent j j) →
        (∀ ⦃i j : J⦄, dependent i j → dependent j i) →
          ∀ (Δ : ℕ),
            (∀ (j : J), (NearlyMinimax.dependentLabelFinset dependent j).card ≤ Δ) →
              ∀ (t B : ℝ),
                0 ≤ t →
                  0 ≤ B →
                    ∀ {E : Type u_2} [inst_2 : MeasurableSpace E] (π : MeasureTheory.Measure E)
                      (a : E → ℝ),
                      Measurable a →
                        (∀ (e : E), |a e| ≤ B) →
                          t * B / NearlyMinimax.historyReferenceRho Δ ≤ 1 / (2 + 8 * (↑Δ : ℝ) ^ 2) →
                            ∀ (F : NearlyMinimax.HistoryMarked dependent E → ℝ),
                              ∫ (h : NearlyMinimax.HistoryMarked dependent E),
                                  F h ∂NearlyMinimax.historyMarkedPrior dependent Δ t π a =
                                NearlyMinimax.historyMarkedExpectation dependent
                                  (NearlyMinimax.historyReferenceRho Δ)
                                  (NearlyMinimax.historyMarkedReference dependent Δ π) a F t)
    (h_NearlyMinimax_historyMarkedDensityDerivative_measurable : ∀ {J : Type u_1} [inst : Fintype J] [inst_1 : LinearOrder J] (dependent : J → J → Prop) (ρ t : ℝ)
      {E : Type u_2} [inst_2 : MeasurableSpace E] (a : E → ℝ),
      Measurable a → Measurable (NearlyMinimax.historyMarkedDensityDerivative dependent ρ t a))
    (h_NearlyMinimax_historyMarkedDensity_measurable : ∀ {J : Type u_1} [inst : Fintype J] [inst_1 : LinearOrder J] (dependent : J → J → Prop) (ρ t : ℝ)
      {E : Type u_2} [inst_2 : MeasurableSpace E] (a : E → ℝ),
      Measurable a → Measurable (NearlyMinimax.historyMarkedDensity dependent ρ t a))
    (h_NearlyMinimax_historyMarkedDensity_hasDerivAt : ∀ {J : Type u_1} [inst : Fintype J] [inst_1 : LinearOrder J] (dependent : J → J → Prop) (ρ t : ℝ)
      {E : Type u_2} (a : E → ℝ) (h : NearlyMinimax.HistoryMarked dependent E),
      HasDerivAt (fun (u : ℝ) ↦ NearlyMinimax.historyMarkedDensity dependent ρ u a h)
        (NearlyMinimax.historyMarkedDensityDerivative dependent ρ t a h) t)
    (h_NearlyMinimax_historyMarkedPriorGenerator_eq_reference : ∀ {J : Type u_1} [inst : Fintype J] [inst_1 : LinearOrder J] (dependent : J → J → Prop),
      (∀ (j : J), dependent j j) →
        ∀ (hsymm : ∀ ⦃i j : J⦄, dependent i j → dependent j i) (Δ : ℕ),
          (∀ (j : J), (NearlyMinimax.dependentLabelFinset dependent j).card ≤ Δ) →
            ∀ (t B : ℝ),
              0 ≤ t →
                0 ≤ B →
                  ∀ {E : Type u_2} [inst_2 : MeasurableSpace E] (π : MeasureTheory.Measure E)
                    [MeasureTheory.IsProbabilityMeasure π] (a : E → ℝ),
                    Measurable a →
                      (∀ (e : E), |a e| ≤ B) →
                        t * B / NearlyMinimax.historyReferenceRho Δ ≤ 1 / (2 + 8 * (↑Δ : ℝ) ^ 2) →
                          ∀ (F : NearlyMinimax.HistoryMarked dependent E → ℝ),
                            NearlyMinimax.historyMarkedPriorGenerator dependent hsymm Δ t π a F =
                              NearlyMinimax.historyMarkedGeneratorExpectation dependent hsymm
                                (NearlyMinimax.historyReferenceRho Δ) t
                                (NearlyMinimax.historyMarkedReference dependent Δ π) π a F)
    (h_NearlyMinimax_historyMarkedDensityDerivative_bound : ∀ {J : Type u_1} [inst : Fintype J] [inst_1 : LinearOrder J] (dependent : J → J → Prop),
      (∀ (j : J), dependent j j) →
        (∀ ⦃i j : J⦄, dependent i j → dependent j i) →
          ∀ (Δ : ℕ),
            (∀ (j : J), (NearlyMinimax.dependentLabelFinset dependent j).card ≤ Δ) →
              ∀ (ρ t B : ℝ),
                0 < ρ →
                  0 ≤ t →
                    0 ≤ B →
                      ∀ {E : Type u_2} [MeasurableSpace E] (a : E → ℝ),
                        (∀ (e : E), |a e| ≤ B) →
                          t * B / ρ ≤ 1 / (2 + 8 * (↑Δ : ℝ) ^ 2) →
                            ∀ (h : NearlyMinimax.HistoryMarked dependent E),
                              |NearlyMinimax.historyMarkedDensityDerivative dependent ρ t a h| ≤
                                ρ⁻¹ * (↑(Fintype.card J) : ℝ) * B * (3 / 2) ^ Fintype.card J)
    (h_NearlyMinimax_historyMarkedDensityDerivative_integral_eq_generator : ∀ {J : Type u_1} [inst : Fintype J] [inst_1 : LinearOrder J] (dependent : J → J → Prop),
      (∀ (j : J), dependent j j) →
        ∀ (hsymm : ∀ ⦃i j : J⦄, dependent i j → dependent j i) (Δ : ℕ),
          1 ≤ Δ →
            (∀ (j : J), (NearlyMinimax.dependentLabelFinset dependent j).card ≤ Δ) →
              ∀ (t B : ℝ),
                0 ≤ t →
                  0 ≤ B →
                    ∀ {E : Type u_2} [inst_2 : MeasurableSpace E] [StandardBorelSpace E]
                      (π : MeasureTheory.Measure E) [MeasureTheory.IsProbabilityMeasure π] (a : E → ℝ),
                      Measurable a →
                        (∀ (e : E), |a e| ≤ B) →
                          t * B / NearlyMinimax.historyReferenceRho Δ ≤ 1 / (2 + 8 * (↑Δ : ℝ) ^ 2) →
                            ∀ (F : NearlyMinimax.HistoryMarked dependent E → ℝ),
                              Measurable F →
                                ∀ (M : ℝ),
                                  0 ≤ M →
                                    (∀ (h : NearlyMinimax.HistoryMarked dependent E), |F h| ≤ M) →
                                      ∫ (h : NearlyMinimax.HistoryMarked dependent E),
                                          F h *
                                            NearlyMinimax.historyMarkedDensityDerivative dependent
                                              (NearlyMinimax.historyReferenceRho Δ) t a
                                              h ∂NearlyMinimax.historyMarkedReference dependent Δ π =
                                        NearlyMinimax.historyMarkedGeneratorExpectation dependent hsymm
                                          (NearlyMinimax.historyReferenceRho Δ) t
                                          (NearlyMinimax.historyMarkedReference dependent Δ π) π a F)
    :
    HasDerivAt (fun u => ∫ h, G u h ∂historyMarkedPrior dependent Δ u π a)
      ((∫ h, G' t h ∂historyMarkedPrior dependent Δ t π a) +
        historyMarkedPriorGenerator dependent hsymm Δ t π a (G t)) t := by
  let μ := historyMarkedReference dependent Δ π
  let _ : IsProbabilityMeasure μ := h_NearlyMinimax_historyMarkedReference_probability dependent hrefl hsymm Δ hΔ hlabels π
  let ρ := historyReferenceRho Δ
  let C : ℝ := (3 / 2 : ℝ) ^ Fintype.card J
  let D : ℝ := ρ⁻¹ * (Fintype.card J : ℝ) * B * C
  have hρ : 0 < ρ := h_NearlyMinimax_historyReferenceRho_pos Δ
  have hC : 0 ≤ C := by positivity
  have hD : 0 ≤ D := by dsimp [D]; positivity
  have hs (u : ℝ) (hu : u ∈ Ioo 0 T) : u * B / ρ ≤ 1 / (2 + 8 * (Δ : ℝ) ^ 2) :=
    (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hu.2.le hB)
      (h_NearlyMinimax_historyReferenceRho_pos Δ).le).trans hsmall
  have hφ (u : ℝ) (hu : u ∈ Ioo 0 T) (h : HistoryMarked dependent E) :
      |historyMarkedDensity dependent ρ u a h| ≤ C := by
    have hb := h_NearlyMinimax_historyMarkedDensity_bounds dependent hrefl hsymm Δ hlabels ρ u B
      (h_NearlyMinimax_historyReferenceRho_pos Δ) hu.1.le hB a habound (hs u hu) h
    have hn : 0 ≤ historyMarkedDensity dependent ρ u a h :=
      (by positivity : (0 : ℝ) ≤ (1 / 2 : ℝ) ^ Fintype.card J).trans hb.1
    rw [abs_of_nonneg hn]
    exact hb.2
  have hφd (u : ℝ) (hu : u ∈ Ioo 0 T) (h : HistoryMarked dependent E) :
      |historyMarkedDensityDerivative dependent ρ u a h| ≤ D :=
    h_NearlyMinimax_historyMarkedDensityDerivative_bound dependent hrefl hsymm Δ hlabels ρ u B
      (h_NearlyMinimax_historyReferenceRho_pos Δ) hu.1.le hB a habound (hs u hu) h
  let H : ℝ → HistoryMarked dependent E → ℝ := fun u h =>
    G u h * historyMarkedDensity dependent ρ u a h
  let H' : ℝ → HistoryMarked dependent E → ℝ := fun u h =>
    G' u h * historyMarkedDensity dependent ρ u a h +
      G u h * historyMarkedDensityDerivative dependent ρ u a h
  have hHM (u : ℝ) : Measurable (H u) :=
    (hGM u).mul (h_NearlyMinimax_historyMarkedDensity_measurable dependent ρ u a ha)
  have hH'M (u : ℝ) : Measurable (H' u) :=
    ((hG'M u).mul (h_NearlyMinimax_historyMarkedDensity_measurable dependent ρ u a ha)).add
      ((hGM u).mul (h_NearlyMinimax_historyMarkedDensityDerivative_measurable dependent ρ u a ha))
  have hHb (u : ℝ) (hu : u ∈ Ioo 0 T) (h : HistoryMarked dependent E) : ‖H u h‖ ≤ M * C := by
    rw [Real.norm_eq_abs, abs_mul]
    exact mul_le_mul (hGb u hu h) (hφ u hu h) (abs_nonneg _) hM
  have hH'b (u : ℝ) (hu : u ∈ Ioo 0 T) (h : HistoryMarked dependent E) :
      ‖H' u h‖ ≤ M' * C + M * D := by
    rw [Real.norm_eq_abs]
    exact (abs_add_le _ _).trans (add_le_add
      (by rw [abs_mul]; exact mul_le_mul (hG'b u hu h) (hφ u hu h) (abs_nonneg _) hM')
      (by rw [abs_mul]; exact mul_le_mul (hGb u hu h) (hφd u hu h) (abs_nonneg _) hM))
  have hi : Integrable (H t) μ := Integrable.of_bound (hHM t).aestronglyMeasurable
    (M * C) (Eventually.of_forall (hHb t ⟨ht, htT⟩))
  have hd := (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := μ) (F := H) (F' := H') (bound := fun _ => M' * C + M * D)
    (s := Ioo 0 T) (Ioo_mem_nhds ht htT)
    (Eventually.of_forall fun u => (hHM u).aestronglyMeasurable)
    hi (hH'M t).aestronglyMeasurable
    (Eventually.of_forall fun h u hu => hH'b u hu h)
    (integrable_const (M' * C + M * D))
    (Eventually.of_forall fun h u hu => (hGD h u hu).mul
      (h_NearlyMinimax_historyMarkedDensity_hasDerivAt dependent ρ u a h))).2
  have hi1 : Integrable (fun h => G' t h * historyMarkedDensity dependent ρ t a h) μ := by
    apply Integrable.of_bound ((hG'M t).mul
      (h_NearlyMinimax_historyMarkedDensity_measurable dependent ρ t a ha)).aestronglyMeasurable (M' * C)
    exact Eventually.of_forall fun h => by
      rw [Real.norm_eq_abs, Pi.mul_apply, abs_mul]
      exact mul_le_mul (hG'b t ⟨ht, htT⟩ h) (hφ t ⟨ht, htT⟩ h) (abs_nonneg _) hM'
  have hi2 : Integrable (fun h => G t h * historyMarkedDensityDerivative dependent ρ t a h) μ := by
    apply Integrable.of_bound ((hGM t).mul
      (h_NearlyMinimax_historyMarkedDensityDerivative_measurable dependent ρ t a ha)).aestronglyMeasurable (M * D)
    exact Eventually.of_forall fun h => by
      rw [Real.norm_eq_abs, Pi.mul_apply, abs_mul]
      exact mul_le_mul (hGb t ⟨ht, htT⟩ h) (hφd t ⟨ht, htT⟩ h) (abs_nonneg _) hM
  have hfirst := h_NearlyMinimax_historyMarkedPrior_integral_eq_expectation dependent hrefl hsymm Δ hlabels
    t B ht.le hB π a ha habound (hs t ⟨ht, htT⟩) (G' t)
  unfold historyMarkedExpectation at hfirst
  have hsecond := h_NearlyMinimax_historyMarkedDensityDerivative_integral_eq_generator dependent hrefl hsymm Δ hΔ hlabels
    t B ht.le hB π a ha habound (hs t ⟨ht, htT⟩) (G t) (hGM t) M hM
      (hGb t ⟨ht, htT⟩)
  rw [← h_NearlyMinimax_historyMarkedPriorGenerator_eq_reference dependent hrefl hsymm Δ hlabels
    t B ht.le hB π a ha habound (hs t ⟨ht, htT⟩) (G t)] at hsecond
  change HasDerivAt (fun u => ∫ h, H u h ∂μ) _ t at hd
  have he : (∫ h, H' t h ∂μ) =
      (∫ h, G' t h ∂historyMarkedPrior dependent Δ t π a) +
        historyMarkedPriorGenerator dependent hsymm Δ t π a (G t) := by
    rw [integral_add hi1 hi2, ← hfirst, hsecond]
  rw [he] at hd
  apply hd.congr_of_eventuallyEq
  filter_upwards [Ioo_mem_nhds ht htT] with u hu
  exact h_NearlyMinimax_historyMarkedPrior_integral_eq_expectation dependent hrefl hsymm Δ hlabels
    u B hu.1.le hB π a ha habound (hs u hu) (G u)
end NearlyMinimax
