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

-- ==== Examples.jtraverso__typed_triangle_absorption.Dependencies.v228ffe4de758.PartitionedTriangleAbsorption.BlowupB.PaddedFractional.PhysicalEdgeModes ====
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
open Finset 
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

def repeatedPairWeight (p : V → Fin t) (i j : Fin t) (g : V → V → ℝ) :
    V → V → V → ℝ :=
  aabLift p i j (fun a b c => (g a c + g b c) / (classSize p i - 2))
def internalPairWeight (p : V → Fin t) (i j : Fin t) (g : V → V → ℝ) :
    V → V → V → ℝ :=
  aabLift p i j (fun a b _c => g a b / classSize p j)

def abcBase (p : V → Fin t) (i j k : Fin t) (h : V → V → V → ℝ)
    (a b c : V) : ℝ :=
  if p a = i ∧ p b = j ∧ p c = k then h a b c else 0
def abcLift (p : V → Fin t) (i j k : Fin t) (h : V → V → V → ℝ) :
    V → V → V → ℝ :=
  pairSymmetrize (fun a b c => abcBase p i j k h a b c + abcBase p i j k h b a c)

def tripartitePairWeight (p : V → Fin t) (i j k : Fin t) (g : V → V → ℝ) :
    V → V → V → ℝ := abcLift p i j k (fun a b _c => g a b / classSize p k)

end PartitionedTriangleAbsorption.BlowupB.PaddedFractional

end
end
end

-- ==== Examples.jtraverso__typed_triangle_absorption.Dependencies.v228ffe4de758.PartitionedTriangleAbsorption.BlowupB.PaddedFractional.PhysicalTypeModes ====
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
open Finset 
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

-- ==== Examples.jtraverso__typed_triangle_absorption.Dependencies.v228ffe4de758.PartitionedTriangleAbsorption.BlowupB.PaddedFstar.Inverse ====
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

-- ==== Examples.jtraverso__typed_triangle_absorption.Dependencies.v228ffe4de758.PartitionedTriangleAbsorption.BlowupB.PaddedComponents.LargeInverseFrame ====
public section
/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
@[expose] public section
/-!
# The inverse frame for classes of size at least 8, and the monochromatic zero-row mode

* `monoPairWeight p i g` puts weight `(g ab + g ac + g bc)/(s - 4)` on the ordered triples of
  distinct vertices of `V_i`. If the class rows of `g` vanish, its load is `g` on the pairs inside
  `V_i` (and `0` elsewhere). This is the zero-row mode of an isolated monochromatic class; it needs
  `s ≥ 5` (in `K₄` it does not exist, see `MonoObstruction.lean`).
* `TernaryInverse₈ F` is `TernaryInverse F` under `8 ≤ γ n`, and
  `completeInverseCert₈_of_ternary` gives `CompleteInverseCert₈ F` for every `F ⊇ F₀` with the same
  allowed pairs.
-/
noncomputable section
namespace PaddedComponents
open Finset PartitionedTriangleAbsorption



open PartitionedTriangleAbsorption.BlowupB.PaddedFractional


section Mode
variable {V : Type*} {t : ℕ} [Fintype V] [DecidableEq V]
/-- The monochromatic zero-row weight. -/
def monoPairWeight (p : V → Fin t) (i : Fin t) (g : V → V → ℝ) (a b c : V) : ℝ :=
  if p a = i ∧ p b = i ∧ p c = i ∧ a ≠ b ∧ a ≠ c ∧ b ≠ c then
    (g a b + g a c + g b c) / (classSize p i - 4) else 0

end Mode

end PaddedComponents

end
end
end

-- ==== Examples.jtraverso__typed_triangle_absorption.Examples.Example_c97da6a07a524a0b6c63_InverseKQ4 ====
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

def zeroRowWeightKQ4 (p : V → Fin 4) (g : V → V → ℝ) (a b c : V) : ℝ :=
  internalPairWeight p 0 1 g a b c +
  repeatedPairWeight p 0 1 g a b c +
  repeatedPairWeight p 0 2 g a b c +
  internalPairWeight p 1 0 g a b c +
  tripartitePairWeight p 1 2 0 g a b c +
  monoPairWeight p 3 g a b c


set_option linter.unusedVariables false in
theorem zeroRowWeightKQ4_bound (p : V → Fin 4) (g : V → V → ℝ) (ε δ : ℝ)
    (hε : 0 ≤ ε) (hδ : 8 ≤ δ) (hg : ∀ a b, |g a b| ≤ ε)
    (hm : ∀ i, δ ≤ classSize p i) (a b c : V) 
    (h_PaddedComponents_monoPairWeight_bound : ∀ {V : Type u_1} {t : ℕ} [inst : Fintype V] [inst_1 : DecidableEq V] (p : V → Fin t) (i : Fin t)
      (g : V → V → ℝ) (ε δ : ℝ),
      0 ≤ ε →
        8 ≤ δ →
          (∀ (a b : V), |g a b| ≤ ε) →
            (∀ (i : Fin t), δ ≤ PartitionedTriangleAbsorption.BlowupB.PaddedFractional.classSize p i) →
              ∀ (a b c : V), |PaddedComponents.monoPairWeight p i g a b c| ≤ 12 * ε / δ)
    (h_PartitionedTriangleAbsorption_BlowupB_PaddedFractional_edgeMode_bounds : ∀ {V : Type u_1} [inst : Fintype V] [inst_1 : DecidableEq V] (p : V → Fin 4) (g : V → V → ℝ)
      (ε δ : ℝ),
      0 ≤ ε →
        4 ≤ δ →
          (∀ (a b : V), |g a b| ≤ ε) →
            (∀ (i : Fin 4), δ ≤ PartitionedTriangleAbsorption.BlowupB.PaddedFractional.classSize p i) →
              ∀ (a b c : V),
                (∀ (i j : Fin 4),
                    |PartitionedTriangleAbsorption.BlowupB.PaddedFractional.internalPairWeight p i j g a
                          b c| ≤
                      12 * ε / δ) ∧
                  (∀ (i j : Fin 4),
                      |PartitionedTriangleAbsorption.BlowupB.PaddedFractional.repeatedPairWeight p i j g
                            a b c| ≤
                        12 * ε / δ) ∧
                    ∀ (i j k : Fin 4),
                      |PartitionedTriangleAbsorption.BlowupB.PaddedFractional.tripartitePairWeight p i j
                            k g a b c| ≤
                        12 * ε / δ)
    :
    |zeroRowWeightKQ4 p g a b c| ≤ 96 * ε / δ := by
  obtain ⟨hi, hr, ht⟩ := h_PartitionedTriangleAbsorption_BlowupB_PaddedFractional_edgeMode_bounds p g ε δ hε (by linarith) hg hm a b c
  have h0 := hi 0 1
  have h1 := hr 0 1
  have h2 := hr 0 2
  have h3 := hi 1 0
  have h4 := ht 1 2 0
  have h5 := h_PaddedComponents_monoPairWeight_bound p 3 g ε δ hε hδ hg hm a b c
  have hpos : 0 ≤ 12 * ε / δ := by
    have : (0 : ℝ) < δ := by linarith
    positivity
  have hM : 96 * ε / δ = 8 * (12 * ε / δ) := by ring
  rw [hM]
  generalize 12 * ε / δ = M at h0 h1 h2 h3 h4 h5 hpos ⊢
  unfold zeroRowWeightKQ4
  rw [abs_le] at h0 h1 h2 h3 h4 h5 ⊢
  constructor <;> linarith [h0.1, h0.2, h1.1, h1.2, h2.1, h2.2, h3.1, h3.2, h4.1, h4.2, h5.1, h5.2]

end PaddedComponents
