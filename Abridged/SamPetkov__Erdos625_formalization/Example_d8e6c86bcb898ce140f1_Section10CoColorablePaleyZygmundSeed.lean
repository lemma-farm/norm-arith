import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.MeasureTheory.Integral.MeanInequalities
import Mathlib.Probability.Distributions.Binomial
import Mathlib.Probability.Moments.SubGaussian
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Data.Sym.NatCard
import Mathlib.Probability.Combinatorics.BinomialRandomGraph.Defs
import Mathlib.Tactic

-- ==== Examples.SamPetkov__Erdos625_formalization.Dependencies.vb467d95511dc.Erdos625.ProbabilityTools ====
section
set_option autoImplicit false
/-!
# Elementary probability tools for Erdős Problem 625

This module gives formally proved versions of the elementary probability
inequalities invoked in Section 1 of the manuscript.  It uses `Measure.real`
for real-valued probabilities, Bochner integrals for real expectations, and
Lebesgue integrals for the extended-nonnegative Paley--Zygmund statement.
-/
open MeasureTheory Set
open scoped ENNReal NNReal ProbabilityTheory
namespace Erdos625
section Markov
variable {Omega : Type*} [MeasurableSpace Omega] {mu : Measure Omega}
end Markov
section PaleyZygmund
variable {Omega : Type*} [MeasurableSpace Omega] {mu : Measure Omega}

/-- Event-notation form of `paleyZygmund_zero_lintegral`, matching (1.5). -/
axiom paleyZygmund_zero {Z : Omega → ℝ≥0∞} (hZ : Measurable Z) :
    (∫⁻ ω, Z ω ∂mu) ^ 2 / (∫⁻ ω, (Z ω) ^ 2 ∂mu) ≤
      mu {ω | 0 < Z ω}
end PaleyZygmund
section SubGaussianTails
open ProbabilityTheory
variable {Omega : Type*} [MeasurableSpace Omega] {mu : Measure Omega}
end SubGaussianTails
section BinomialTail
open ProbabilityTheory
end BinomialTail
end Erdos625

end

-- ==== Examples.SamPetkov__Erdos625_formalization.Dependencies.vb467d95511dc.Erdos625.GraphModel ====
section
set_option autoImplicit false
/-!
# Graph invariants for Erdős Problem 625

This file defines cocolourings and the cochromatic number.  Empty colour
classes are permitted, so a cocolouring with `k` colours represents a
partition into at most `k` nonempty clique-or-independent parts.
-/
namespace Erdos625
universe u v
/-- A labelled simple graph on `n` vertices. -/
abbrev LabeledGraph (n : ℕ) := SimpleGraph (Fin n)
/-- The two allowed kinds of parts in a cocolouring. -/
inductive PartKind where
  | independent
  | clique
  deriving DecidableEq
/-- A colouring in which every colour class is independently declared to be
an independent set or a clique. -/
structure CoColoring {V : Type u} (G : SimpleGraph V) (κ : Type v) where
  color : V → κ
  kind : κ → PartKind
  valid : ∀ c,
    match kind c with
    | .independent => G.IsIndepSet {v | color v = c}
    | .clique => G.IsClique {v | color v = c}
namespace CoColoring
variable {V : Type u} {κ : Type v} {κ₂ : Type*} {G : SimpleGraph V}

end CoColoring
/-- A graph is cocolourable with at most `k` parts. -/
def CoColorable {V : Type u} (G : SimpleGraph V) (k : ℕ) : Prop :=
  Nonempty (CoColoring G (Fin k))
variable {V : Type u} {G : SimpleGraph V} {k : ℕ}

end Erdos625

end

-- ==== Examples.SamPetkov__Erdos625_formalization.Dependencies.vb467d95511dc.Erdos625.Target ====
section
set_option autoImplicit false
/-!
# Exact formal target

The proposition `Erdos625Statement` is the exact full-sequence probability
claim from the manuscript.  The final theorem proving it is
`Erdos625.erdos625`.
-/
namespace Erdos625
open Filter MeasureTheory
/-- The edge probability lies in the unit interval.  Naming this elementary
proof keeps the protected challenge declaration byte-for-byte comparable. -/
axiom halfProbability_mem : (1 : ℝ) / 2 ∈ Set.Icc (0 : ℝ) 1
/-- The edge probability `1/2`, packaged as a point of the unit interval. -/
noncomputable def halfProbability : unitInterval :=
  ⟨(1 : ℝ) / 2, halfProbability_mem⟩

/-- The law `G(n,1/2)` on labelled simple graphs with vertex type `Fin n`. -/
noncomputable def randomGraphMeasure (n : ℕ) : Measure (LabeledGraph n) :=
  SimpleGraph.binomialRandom (Fin n) halfProbability
set_option linter.unusedVariables false in
axiom _root_.Erdos625.instIsProbabilityMeasureRandomGraph : ∀ (n : ℕ), MeasureTheory.IsProbabilityMeasure (Erdos625.randomGraphMeasure n)
attribute [instance] _root_.Erdos625.instIsProbabilityMeasureRandomGraph

end Erdos625

end

-- ==== Examples.SamPetkov__Erdos625_formalization.Examples.Example_d8e6c86bcb898ce140f1_Section10CoColorablePaleyZygmundSeed ====
set_option autoImplicit false
/-!
# Sections IX--X: count-to-cocolourable real seed

This module is a generic second-moment adapter.  The construction and moment
estimates for the count remain entirely external inputs.
-/
namespace Erdos625
open MeasureTheory Set
open scoped ENNReal NNReal ProbabilityTheory
/-- Any measurable nonnegative count whose positivity certifies a
`k`-cocolouring supplies the corresponding real-valued Paley--Zygmund seed
under the random-graph law. -/
theorem coColorable_real_seed_of_count
    (n k : Nat) (Z : LabeledGraph n -> ENNReal)
    (hZ : Measurable Z)
    (hPositive : ∀ G, 0 < Z G -> CoColorable G k) :
    (((∫⁻ G, Z G ∂(randomGraphMeasure n)) ^ 2 /
        (∫⁻ G, (Z G) ^ 2 ∂(randomGraphMeasure n))).toReal ≤
      (randomGraphMeasure n).real {G | CoColorable G k}) := by
  have hPZ := paleyZygmund_zero (mu := randomGraphMeasure n) hZ
  have hMono :
      (randomGraphMeasure n) {G | 0 < Z G} ≤
        (randomGraphMeasure n) {G | CoColorable G k} := by
    apply measure_mono
    intro G hG
    exact hPositive G hG
  have hENN :
      (∫⁻ G, Z G ∂(randomGraphMeasure n)) ^ 2 /
          (∫⁻ G, (Z G) ^ 2 ∂(randomGraphMeasure n)) ≤
        (randomGraphMeasure n) {G | CoColorable G k} :=
    hPZ.trans hMono
  rw [Measure.real]
  apply (ENNReal.toReal_le_toReal
    (ne_top_of_le_ne_top
      (measure_ne_top (randomGraphMeasure n) {G | CoColorable G k}) hENN)
    (measure_ne_top (randomGraphMeasure n) {G | CoColorable G k})).2
  exact hENN
end Erdos625
