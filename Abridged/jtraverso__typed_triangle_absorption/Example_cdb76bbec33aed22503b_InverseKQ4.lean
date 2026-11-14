module

public import Std
public import Mathlib.Algebra.Ring.Parity
public import Mathlib.Algebra.BigOperators.Group.Finset.Pi
public import Mathlib.Data.Finset.Powerset
public import Mathlib.Data.Finset.Sym
public import Mathlib.Basic.Real.Basic
public import Mathlib.Combinatorics.SimpleGraph.Clique
public import Mathlib.Combinatorics.SimpleGraph.Finite
public import Mathlib.Algebra.BigOperators.Pi
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Ring
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Tactic.FinCases
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Tactic.Linarith
public import Mathlib.Data.Finset.Union
public import Mathlib.Data.Sym.Sym2
public import Mathlib.Algebra.Module.Pi
public import Mathlib.Tactic.Push
public import Mathlib.GroupTheory.Perm.Fin
public import Mathlib.Tactic.DeriveFintype
public import Mathlib.Algebra.Group.Subgroup.Basic
public import Mathlib.Tactic.Abel
public import Mathlib.Data.Finset.Prod
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
public import Mathlib.Data.Fintype.Sigma
public import Mathlib.Tactic.SplitIfs
public import Mathlib.Tactic
public import Mathlib.Logic.Equiv.Fintype
public import Mathlib.Data.Fintype.Perm
public import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
public import Mathlib.Data.Nat.Choose.Bounds
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Positivity
public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.Algebra.Order.Field.GeomSum
public import Mathlib.Tactic.GCongr
public import Mathlib.Combinatorics.Hall.Finite
public import Mathlib.Data.Finset.Sum
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Data.Nat.Log
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Data.Nat.Cast.Order.Field
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.Data.Fintype.Fin
public import Mathlib.Topology.MetricSpace.CauSeqFilter
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Analysis.Normed.Group.InfiniteSum
public import Mathlib.Analysis.Convex.SpecificFunctions.Basic
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Algebra.BigOperators.Field
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Combinatorics.SimpleGraph.DeleteEdges
public import Mathlib.Algebra.Module.BigOperators
public import Mathlib.Data.Int.Interval
public import Mathlib.Probability.Independence.Basic
public import Mathlib.Probability.Distributions.Bernoulli
public import Mathlib.Probability.Moments.SubGaussian
public import Mathlib.Analysis.SpecialFunctions.Exponential
public import Mathlib.Analysis.Complex.ExponentialBounds
public import Mathlib.Combinatorics.SimpleGraph.DegreeSum
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.Algebra.Order.Floor.Semiring
public import Mathlib.Logic.Equiv.Basic
public import Mathlib.Order.Interval.Finset.Nat

-- ==== Examples.jtraverso__typed_triangle_absorption.Dependencies.v917af0cf750a.PartitionedTriangleAbsorption.TypedTransformerLabels ====
public section
/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
/-! # Auxiliary types for the eleven-edge transformer

The finite link tests below produce auxiliary parts for F0--F3. They do not
construct a universal refiner or an embedding in a prescribed host graph.
-/
@[expose] public section
namespace PartitionedTriangleAbsorption.TypedTransformer
open Finset  
variable {t : ℕ}
/-- A link edge records an allowed triangle, retaining repeated parts. -/
def Link (F : Finset (Multiset (Fin t))) (r a b : Fin t) : Prop :=
  ({r, a, b} : Multiset (Fin t)) ∈ F

variable {W : Type*} [DecidableEq W] {I : Type*} [Fintype I]

end PartitionedTriangleAbsorption.TypedTransformer

end
end

-- ==== Examples.jtraverso__typed_triangle_absorption.Dependencies.v917af0cf750a.PartitionedTriangleAbsorption.BlowupB.PaddedFractional.CompletePhysical ====
public section
/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
@[expose] public section
/-!
# Physical ternary weights in the complete graph of allowed pairs
-/
namespace PartitionedTriangleAbsorption.BlowupB.PaddedFractional
open Finset TypedTransformer
variable {V : Type*} {t : ℕ}

def AdmissibleTriple (p : V → Fin t) (F : Finset (Multiset (Fin t))) (a b c : V) : Prop :=
  a ≠ b ∧ a ≠ c ∧ b ≠ c ∧ Link F (p a) (p b) (p c)

def TernarySupported (p : V → Fin t) (F : Finset (Multiset (Fin t)))
    (w : V → V → V → ℝ) : Prop :=
  ∀ a b c, ¬ AdmissibleTriple p F a b c → w a b c = 0

end PartitionedTriangleAbsorption.BlowupB.PaddedFractional

end
end

-- ==== Examples.jtraverso__typed_triangle_absorption.Dependencies.v917af0cf750a.PartitionedTriangleAbsorption.BlowupB.PaddedFractional.PhysicalEdgeModes ====
public section
/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
@[expose] public section
/-!
# Physical lifts of the zero-row edge modes

All weights here are functions on actual vertices.  An oriented repeated-class
block is symmetrized in the three possible positions of its singleton class.
-/
noncomputable section
namespace PartitionedTriangleAbsorption.BlowupB.PaddedFractional
open Finset TypedTransformer
variable {V : Type*} {t : ℕ} [Fintype V] [DecidableEq V]
def classVertices (p : V → Fin t) (i : Fin t) : Finset V := univ.filter (p · = i)

def classSize (p : V → Fin t) (i : Fin t) : ℝ := (classVertices p i).card

def pairSymmetrize (f : V → V → V → ℝ) (a b c : V) : ℝ :=
  f a b c + f a c b + f b c a

def aabBase (p : V → Fin t) (i j : Fin t) (h : V → V → V → ℝ)
    (a b c : V) : ℝ :=
  if p a = i ∧ p b = i ∧ p c = j ∧ a ≠ b then h a b c else 0
def aabLift (p : V → Fin t) (i j : Fin t) (h : V → V → V → ℝ) :
    V → V → V → ℝ := pairSymmetrize (aabBase p i j h)

def abcBase (p : V → Fin t) (i j k : Fin t) (h : V → V → V → ℝ)
    (a b c : V) : ℝ :=
  if p a = i ∧ p b = j ∧ p c = k then h a b c else 0
def abcLift (p : V → Fin t) (i j k : Fin t) (h : V → V → V → ℝ) :
    V → V → V → ℝ :=
  pairSymmetrize (fun a b c => abcBase p i j k h a b c + abcBase p i j k h b a c)

end PartitionedTriangleAbsorption.BlowupB.PaddedFractional

end
end
end

-- ==== Examples.jtraverso__typed_triangle_absorption.Dependencies.v917af0cf750a.PartitionedTriangleAbsorption.BlowupB.PaddedFractional.PhysicalTypeModes ====
public section
/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
@[expose] public section
/-! # Uniform physical lifts of the global class totals -/
noncomputable section
namespace PartitionedTriangleAbsorption.BlowupB.PaddedFractional
open Finset TypedTransformer
variable {V : Type*} {t : ℕ} [Fintype V] [DecidableEq V]

def repeatedTypeWeight (p : V → Fin t) (i j : Fin t) (z : ℝ) : V → V → V → ℝ :=
  aabLift p i j (fun _a _b _c =>
    2 * z / (classSize p i * (classSize p i - 1) * classSize p j))
def tripartiteTypeWeight (p : V → Fin t) (i j k : Fin t) (z : ℝ) : V → V → V → ℝ :=
  abcLift p i j k (fun _a _b _c => z / (classSize p i * classSize p j * classSize p k))

end PartitionedTriangleAbsorption.BlowupB.PaddedFractional

end
end
end

-- ==== Examples.jtraverso__typed_triangle_absorption.Dependencies.v917af0cf750a.PartitionedTriangleAbsorption.BlowupB.PaddedFstar.Inverse ====
public section
/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
@[expose] public section
/-!
# The bounded signed inverse for F*

Totals use a new MONOCHROMATIC mode (`monoTypeWeight`, type `iii`) for 000 and 333, together with
repeated and tripartite modes. The type vectors span all seven allowed total coordinates, so no
compatibility condition is needed. Vertex rows and zero rows use only existing modes (no
monochromatic one). The bound `2^20 ε/(γ^6 n)` of the F₁/F₂ inverse is kept.
-/
noncomputable section
namespace PaddedFstar
open Finset PartitionedTriangleAbsorption
open PartitionedTriangleAbsorption.TypedTransformer


open PartitionedTriangleAbsorption.BlowupB.PaddedFractional

variable {V : Type*} [Fintype V] [DecidableEq V]
set_option linter.unusedSectionVars false
/-! ### The monochromatic mode -/
/-- Uniform weight `z` of type `iii`, spread over the ordered triples of distinct `V_i`-vertices. -/
def monoTypeWeight (p : V → Fin 4) (i : Fin 4) (z : ℝ) (a b c : V) : ℝ :=
  if p a = i ∧ p b = i ∧ p c = i ∧ a ≠ b ∧ a ≠ c ∧ b ≠ c then
    6 * z / (classSize p i * (classSize p i - 1) * (classSize p i - 2)) else 0





/-! ### Stage 1: totals -/








/-! ### Stage 2: vertex rows -/





/-! ### Stage 3: zero rows -/





/-! ### The complete inverse and the certificate -/


end PaddedFstar

end
end
end

-- ==== Examples.jtraverso__typed_triangle_absorption.Dependencies.v917af0cf750a.PartitionedTriangleAbsorption.BlowupB.Kappa.G3Families ====
public section
/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
@[expose] public section
/-!
# The eleven disconnected `ThreeStepLinks` classes with charged components

`KQ1`–`KQ11` (census rows "Y | * | 2,3 | * | charges", relabelled so that a charged component
contains the class `0`). Each charged component: one charge of unit `12` (or `6` for `KQ10`),
`χ ≡ const ≢ 0 mod 3`, generic templates of charge `±U`. `KQ3` has two charged components.
Generator: `gen_g3.py`.
-/
noncomputable section
namespace PaddedComponents
open Finset PartitionedTriangleAbsorption
open PartitionedTriangleAbsorption.TypedTransformer





-- Census class `000 112 113 123`.
/-- `{001 002 012 333}`. -/
noncomputable def KQ1 : Finset (Multiset (Fin 4)) := {{0, 0, 1}, {0, 0, 2}, {0, 1, 2}, {3, 3, 3}}

-- Census class `000 001 223 233`.

-- Census class `001 011 223 233`.

-- Census class `000 112 113 122 123`.
/-- `{001 002 011 012 333}`. -/
noncomputable def KQ4 : Finset (Multiset (Fin 4)) := {{0, 0, 1}, {0, 0, 2}, {0, 1, 1}, {0, 1, 2}, {3, 3, 3}}

-- Census class `000 112 113 122 133`.

-- Census class `000 001 011 223 233`.

-- Census class `000 112 113 122 123 133`.

-- Census class `000 112 113 123 223 233`.

-- Census class `000 001 011 111 223 233`.

-- Census class `000 112 113 122 133 223 233`.

-- Census class `000 111 223 233`.

end PaddedComponents

end
end
end

-- ==== Examples.jtraverso__typed_triangle_absorption.Examples.Example_cdb76bbec33aed22503b_InverseKQ4 ====
/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
@[expose] public section
/-!
# The bounded signed inverse for `KQ4` (classes of size at least 8)

Same frame as Aristotle's `InverseFMxx` (generator `gen_km.py`): totals from the types
`001` `002` `011` `012` `333`; vertex rows from repeated, singleton, tripartite and monochromatic vertex
modes (per-mode budgets `12 m D/δ²`, `24 m D/δ²` for coefficient mass `m`); zero rows from
internal, repeated and tripartite pair modes and the monochromatic zero-row mode of class `3`.
-/
noncomputable section
namespace PaddedComponents
open Finset PartitionedTriangleAbsorption
open PartitionedTriangleAbsorption.TypedTransformer


open PartitionedTriangleAbsorption.BlowupB.PaddedFractional

open PaddedFstar  
variable {V : Type*} [Fintype V] [DecidableEq V]
set_option linter.unusedSectionVars false
set_option maxHeartbeats 8000000

def typeWeightKQ4 (p : V → Fin 4) (z001 z002 z011 z012 z333 : ℝ) (a b c : V) : ℝ :=
  repeatedTypeWeight p 0 1 z001 a b c +
  repeatedTypeWeight p 0 2 z002 a b c +
  repeatedTypeWeight p 1 0 z011 a b c +
  tripartiteTypeWeight p 0 1 2 z012 a b c +
  monoTypeWeight p 3 z333 a b c


set_option linter.unusedVariables false in
theorem typeWeightKQ4_bound (p : V → Fin 4) (z001 z002 z011 z012 z333 E δ : ℝ)
    (hE : 0 ≤ E) (hδ : 4 ≤ δ) (hz001 : |z001| ≤ 8 * E) (hz002 : |z002| ≤ 8 * E) (hz011 : |z011| ≤ 8 * E) (hz012 : |z012| ≤ 8 * E) (hz333 : |z333| ≤ 2 * E)
    (hm : ∀ i, δ ≤ classSize p i) (a b c : V) 
    (h_PaddedFstar_mono_normalizer_bound : ∀ {V : Type u_1} [inst : Fintype V] [DecidableEq V] (p : V → Fin 4) (i : Fin 4) (z E δ : ℝ),
      0 ≤ E →
        4 ≤ δ →
          |z| ≤ 2 * E →
            (∀ (i : Fin 4), δ ≤ PartitionedTriangleAbsorption.BlowupB.PaddedFractional.classSize p i) →
              |6 * z /
                    (PartitionedTriangleAbsorption.BlowupB.PaddedFractional.classSize p i *
                        (PartitionedTriangleAbsorption.BlowupB.PaddedFractional.classSize p i - 1) *
                      (PartitionedTriangleAbsorption.BlowupB.PaddedFractional.classSize p i - 2))| ≤
                32 * E / δ ^ 3)
    (h_PartitionedTriangleAbsorption_BlowupB_PaddedFractional_repeatedType_normalizer_bound : ∀ {V : Type u_1} {t : ℕ} [inst : Fintype V] [DecidableEq V] (p : V → Fin t) (i j : Fin t)
      (z E δ : ℝ),
      0 ≤ E →
        4 ≤ δ →
          |z| ≤ 8 * E →
            (∀ (i : Fin t), δ ≤ PartitionedTriangleAbsorption.BlowupB.PaddedFractional.classSize p i) →
              |2 * z /
                    (PartitionedTriangleAbsorption.BlowupB.PaddedFractional.classSize p i *
                        (PartitionedTriangleAbsorption.BlowupB.PaddedFractional.classSize p i - 1) *
                      PartitionedTriangleAbsorption.BlowupB.PaddedFractional.classSize p j)| ≤
                32 * E / δ ^ 3)
    (h_PaddedComponents_typeWeightKQ4_supported : ∀ {V : Type u_1} [inst : Fintype V] [inst_1 : DecidableEq V] (p : V → Fin 4)
      (z001 z002 z011 z012 z333 : ℝ),
      PartitionedTriangleAbsorption.BlowupB.PaddedFractional.TernarySupported p PaddedComponents.KQ4
        (PaddedComponents.typeWeightKQ4 p z001 z002 z011 z012 z333))
    (h_PartitionedTriangleAbsorption_BlowupB_PaddedFractional_tripartiteType_normalizer_bound : ∀ {V : Type u_1} {t : ℕ} [inst : Fintype V] [DecidableEq V] (p : V → Fin t) (i j k : Fin t)
      (z E δ : ℝ),
      0 ≤ E →
        4 ≤ δ →
          |z| ≤ 8 * E →
            (∀ (i : Fin t), δ ≤ PartitionedTriangleAbsorption.BlowupB.PaddedFractional.classSize p i) →
              |z /
                    (PartitionedTriangleAbsorption.BlowupB.PaddedFractional.classSize p i *
                        PartitionedTriangleAbsorption.BlowupB.PaddedFractional.classSize p j *
                      PartitionedTriangleAbsorption.BlowupB.PaddedFractional.classSize p k)| ≤
                32 * E / δ ^ 3)
    :
    |typeWeightKQ4 p z001 z002 z011 z012 z333 a b c| ≤ 32 * E / δ ^ 3 := by
  have hM : 0 ≤ 32 * E / δ ^ 3 := by positivity
  have hsup := h_PaddedComponents_typeWeightKQ4_supported p z001 z002 z011 z012 z333
  by_cases hdiag : a = b ∨ a = c ∨ b = c
  · have hbad : ¬ AdmissibleTriple p KQ4 a b c := by
      intro h
      rcases hdiag with hdiag | hdiag | hdiag
      · exact h.1 hdiag
      · exact h.2.1 hdiag
      · exact h.2.2.1 hdiag
    rw [hsup a b c hbad, abs_zero]
    exact hM
  have hab : a ≠ b := fun h => hdiag (Or.inl h)
  have hac : a ≠ c := fun h => hdiag (Or.inr (Or.inl h))
  have hbc : b ≠ c := fun h => hdiag (Or.inr (Or.inr h))
  have e0 := h_PartitionedTriangleAbsorption_BlowupB_PaddedFractional_repeatedType_normalizer_bound p 0 1 z001 E δ hE hδ hz001 hm
  have e1 := h_PartitionedTriangleAbsorption_BlowupB_PaddedFractional_repeatedType_normalizer_bound p 0 2 z002 E δ hE hδ hz002 hm
  have e2 := h_PartitionedTriangleAbsorption_BlowupB_PaddedFractional_repeatedType_normalizer_bound p 1 0 z011 E δ hE hδ hz011 hm
  have e3 := h_PartitionedTriangleAbsorption_BlowupB_PaddedFractional_tripartiteType_normalizer_bound p 0 1 2 z012 E δ hE hδ hz012 hm
  have e4 := h_PaddedFstar_mono_normalizer_bound p 3 z333 E δ hE hδ hz333 hm
  dsimp only [typeWeightKQ4, monoTypeWeight, repeatedTypeWeight, tripartiteTypeWeight,
    aabLift, abcLift, pairSymmetrize, aabBase, abcBase]
  generalize ha : p a = i
  generalize hb : p b = j
  generalize hc : p c = k
  fin_cases i <;> fin_cases j <;> fin_cases k <;>
    simp [hab, hac, hbc]
  all_goals first
    | exact e0
    | exact e1
    | exact e2
    | exact e3
    | exact e4
    | exact hM

end PaddedComponents
