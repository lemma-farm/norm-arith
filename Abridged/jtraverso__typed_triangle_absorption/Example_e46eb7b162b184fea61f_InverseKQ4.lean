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

-- ==== Examples.jtraverso__typed_triangle_absorption.Dependencies.v228ffe4de758.PartitionedTriangleAbsorption.TypedTransformerLabels ====
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

-- ==== Examples.jtraverso__typed_triangle_absorption.Dependencies.v228ffe4de758.PartitionedTriangleAbsorption.BlowupB.PaddedFractional.CompletePhysical ====
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
def TernarySymmetric (w : V → V → V → ℝ) : Prop :=
  (∀ a b c, w a b c = w b a c) ∧ (∀ a b c, w a b c = w a c b)
def TernarySupported (p : V → Fin t) (F : Finset (Multiset (Fin t)))
    (w : V → V → V → ℝ) : Prop :=
  ∀ a b c, ¬ AdmissibleTriple p F a b c → w a b c = 0
def ternaryLoad [Fintype V] (w : V → V → V → ℝ) (a b : V) : ℝ := ∑ c, w a b c

end PartitionedTriangleAbsorption.BlowupB.PaddedFractional

end
end

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
open Finset TypedTransformer
variable {V : Type*} {t : ℕ} [Fintype V] [DecidableEq V]
def classVertices (p : V → Fin t) (i : Fin t) : Finset V := univ.filter (p · = i)

def classSize (p : V → Fin t) (i : Fin t) : ℝ := (classVertices p i).card
def ClassRowsZero (p : V → Fin t) (g : V → V → ℝ) : Prop :=
  ∀ a i, ∑ b ∈ classVertices p i, g a b = 0
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

-- ==== Examples.jtraverso__typed_triangle_absorption.Dependencies.v228ffe4de758.PartitionedTriangleAbsorption.BlowupB.PaddedFractional.PhysicalVertexModes ====
public section
/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
@[expose] public section
/-! # Physical corrections of vertex-to-class rows -/
noncomputable section
namespace PartitionedTriangleAbsorption.BlowupB.PaddedFractional
open Finset TypedTransformer
variable {V : Type*} {t : ℕ} [Fintype V] [DecidableEq V]
def classRow (p : V → Fin t) (g : V → V → ℝ) (a : V) (k : Fin t) : ℝ :=
  ∑ b ∈ classVertices p k, g a b

def vertexInternalKernel (p : V → Fin t) (i : Fin t) (f : V → ℝ) (a b : V) : ℝ :=
  if p a = i ∧ p b = i then
    if a ≠ b then (f a + f b) / (classSize p i - 2) else 0 else 0

def repeatedVertexWeight (p : V → Fin t) (i j : Fin t) (f : V → ℝ) : V → V → V → ℝ :=
  aabLift p i j (fun a b _c => (f a + f b) / ((classSize p i - 2) * classSize p j))

def singletonVertexWeight (p : V → Fin t) (i j : Fin t) (f : V → ℝ) : V → V → V → ℝ :=
  aabLift p i j (fun _a _b c => 2 * f c / (classSize p i * (classSize p i - 1)))

def tripartiteVertexWeight (p : V → Fin t) (i j k : Fin t) (f : V → ℝ) : V → V → V → ℝ :=
  abcLift p i j k (fun a _b _c => f a / (classSize p j * classSize p k))

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
open Finset TypedTransformer
variable {V : Type*} {t : ℕ} [Fintype V] [DecidableEq V]
def classTotal (p : V → Fin t) (g : V → V → ℝ) (i j : Fin t) : ℝ :=
  ∑ a ∈ classVertices p i, classRow p g a j

def repeatedTypeWeight (p : V → Fin t) (i j : Fin t) (z : ℝ) : V → V → V → ℝ :=
  aabLift p i j (fun _a _b _c =>
    2 * z / (classSize p i * (classSize p i - 1) * classSize p j))
def tripartiteTypeWeight (p : V → Fin t) (i j k : Fin t) (z : ℝ) : V → V → V → ℝ :=
  abcLift p i j k (fun _a _b _c => z / (classSize p i * classSize p j * classSize p k))

end PartitionedTriangleAbsorption.BlowupB.PaddedFractional

end
end
end

-- ==== Examples.jtraverso__typed_triangle_absorption.Dependencies.v228ffe4de758.PartitionedTriangleAbsorption.BlowupB.PaddedF12.TypeInverse ====
public section
/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
@[expose] public section
/-! # The bounded physical correction of all global type totals -/
noncomputable section
namespace PartitionedTriangleAbsorption.BlowupB.PaddedFractional
open Finset TypedTransformer 
variable {V : Type*} [Fintype V] [DecidableEq V]
def EdgeSupported (p : V → Fin 4) (F : Finset (Multiset (Fin 4))) (g : V → V → ℝ) : Prop :=
  ∀ a b, (¬ ∃ k, Link F (p a) (p b) k) → g a b = 0

end PartitionedTriangleAbsorption.BlowupB.PaddedFractional

end
end
end

-- ==== Examples.jtraverso__typed_triangle_absorption.Dependencies.v228ffe4de758.PartitionedTriangleAbsorption.BlowupB.PaddedFractional.VertexInverse ====
public section
/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
@[expose] public section
/-! # Solving every vertex-to-class row with the F₁ and F₂ links -/
noncomputable section
namespace PartitionedTriangleAbsorption.BlowupB.PaddedFractional
open Finset TypedTransformer 
variable {V : Type*} [Fintype V] [DecidableEq V]
def VertexDemandZero (p : V → Fin 4) (d : V → Fin 4 → ℝ) : Prop :=
  ∀ i j, ∑ a ∈ classVertices p i, d a j = 0
def VertexDemandSupported (p : V → Fin 4) (F : Finset (Multiset (Fin 4)))
    (d : V → Fin 4 → ℝ) : Prop :=
  ∀ a j, (¬ ∃ k, Link F (p a) j k) → d a j = 0

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

-- ==== Examples.jtraverso__typed_triangle_absorption.Dependencies.v228ffe4de758.PartitionedTriangleAbsorption.BlowupB.PaddedNoCommon.InverseFrame ====
public section
/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
@[expose] public section
/-!
# Framework for the complete signed inverse of the six base families

`TernaryInverse F` is the ternary form of the bounded signed inverse (symmetric ternary weights
supported on `F`-admissible triples, with load equal to any bounded `F`-supported symmetric demand
and every weight at most `2^20 ε/(γ^6 n)`). It needs no compatibility condition: the six base
families have type vectors spanning all allowed class-pair coordinates.

`completeInverseCert_of_ternary` turns it into `CompleteInverseCert F` for every `F ⊇ F0` with the
same allowed pairs (the copy step of the F* / Fbit certificates).

`lc d a₀ a₁ a₂ a₃` is a linear combination of the four row demands of a vertex; it is used as the
input of the vertex modes.
-/
noncomputable section
namespace PaddedNoCommon
open Finset PartitionedTriangleAbsorption
open PartitionedTriangleAbsorption.TypedTransformer


open PartitionedTriangleAbsorption.BlowupB.PaddedFractional



variable {V : Type*} [Fintype V] [DecidableEq V]
/-- A linear combination of the four row demands of a vertex. -/
def lc (d : V → Fin 4 → ℝ) (a0 a1 a2 a3 : ℝ) (v : V) : ℝ :=
  a0 * d v 0 + a1 * d v 1 + a2 * d v 2 + a3 * d v 3

end PaddedNoCommon

end
end
end

-- ==== Examples.jtraverso__typed_triangle_absorption.Dependencies.v228ffe4de758.PartitionedTriangleAbsorption.BlowupB.PaddedComponents.MonoVertexMode ====
public section
/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
@[expose] public section
/-!
# The monochromatic vertex mode

`monoVertexWeight p i f` puts weight `(f a + f b + f c) / ((s - 2)(s - 3))` (`s = |V_i|`) on every
ordered triple of distinct vertices of `V_i`. If `∑_{V_i} f = 0` its load is the internal vertex
kernel `(f a + f b)/(s - 2)` on `V_i`, so its only nonzero rows are `row(a, i) = f a` for `a ∈ V_i`.

This corrects the row of a vertex towards its own class using only the type `{i, i, i}`. It is the
vertex mode that was missing for families in which a class sees its own class only through
`{i,i,i}` (for instance `{000, 001}`: a class-0 vertex has rows `0` and `1`, and `001` alone
moves both together).
-/
noncomputable section
namespace PaddedComponents
open Finset PartitionedTriangleAbsorption
open PartitionedTriangleAbsorption.TypedTransformer
open PartitionedTriangleAbsorption.BlowupB.PaddedFractional
variable {V : Type*} {t : ℕ} [Fintype V] [DecidableEq V]
/-- The monochromatic vertex weight. -/
def monoVertexWeight (p : V → Fin t) (i : Fin t) (f : V → ℝ) (a b c : V) : ℝ :=
  if p a = i ∧ p b = i ∧ p c = i ∧ a ≠ b ∧ a ≠ c ∧ b ≠ c then
    (f a + f b + f c) / ((classSize p i - 2) * (classSize p i - 3)) else 0

end PaddedComponents

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
open PartitionedTriangleAbsorption.TypedTransformer


open PartitionedTriangleAbsorption.BlowupB.PaddedFractional

open   PaddedNoCommon
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

-- ==== Examples.jtraverso__typed_triangle_absorption.Dependencies.v228ffe4de758.PartitionedTriangleAbsorption.BlowupB.Kappa.G3Families ====
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




open   PaddedNoCommon 
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

-- ==== Examples.jtraverso__typed_triangle_absorption.Examples.Example_e46eb7b162b184fea61f_InverseKQ4 ====
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

open PaddedFstar PaddedNoCommon 
variable {V : Type*} [Fintype V] [DecidableEq V]
set_option linter.unusedSectionVars false
set_option maxHeartbeats 8000000

def typeWeightKQ4 (p : V → Fin 4) (z001 z002 z011 z012 z333 : ℝ) (a b c : V) : ℝ :=
  repeatedTypeWeight p 0 1 z001 a b c +
  repeatedTypeWeight p 0 2 z002 a b c +
  repeatedTypeWeight p 1 0 z011 a b c +
  tripartiteTypeWeight p 0 1 2 z012 a b c +
  monoTypeWeight p 3 z333 a b c

/-- The real compatibility of `KQ4` on class totals (the charge vanishes on the totals). -/
def CompatKQ4 (p : V → Fin 4) (g : V → V → ℝ) : Prop :=
  (1 : ℝ) * classTotal p g 0 0 + (-1 : ℝ) * classTotal p g 0 1 + (-1 : ℝ) * classTotal p g 0 2 + (1 : ℝ) * classTotal p g 1 1 + (2 : ℝ) * classTotal p g 1 2 = 0

def vertexWeightKQ4 (p : V → Fin 4) (d : V → Fin 4 → ℝ) (a b c : V) : ℝ :=
  repeatedVertexWeight p 0 1 (lc d 1 0 0 0) a b c +
  singletonVertexWeight p 1 0 (lc d (-1 / 2) (1 / 2) (-1 / 2) 0) a b c +
  tripartiteVertexWeight p 0 1 2 (lc d 0 0 1 0) a b c +
  singletonVertexWeight p 0 1 (lc d (1 / 2) (-1 / 2) (-1 / 2) 0) a b c +
  repeatedVertexWeight p 1 0 (lc d 0 1 0 0) a b c +
  tripartiteVertexWeight p 1 0 2 (lc d 0 0 1 0) a b c +
  singletonVertexWeight p 0 2 (lc d (1 / 2) (-1 / 2) 0 0) a b c +
  tripartiteVertexWeight p 2 0 1 (lc d 0 1 0 0) a b c +
  monoVertexWeight p 3 (lc d 0 0 0 1) a b c

def zeroRowWeightKQ4 (p : V → Fin 4) (g : V → V → ℝ) (a b c : V) : ℝ :=
  internalPairWeight p 0 1 g a b c +
  repeatedPairWeight p 0 1 g a b c +
  repeatedPairWeight p 0 2 g a b c +
  internalPairWeight p 1 0 g a b c +
  tripartitePairWeight p 1 2 0 g a b c +
  monoPairWeight p 3 g a b c


set_option linter.unusedVariables false in
/-- **The ternary bounded signed inverse for `KQ4` (classes of size at least 8).** -/
theorem ternaryInverse₈_KQ4 (V : Type) [Fintype V] [DecidableEq V] (p : V → Fin 4)
    (g : V → V → ℝ) (ε γ : ℝ) (hε : 0 ≤ ε) (hγ : 0 < γ) (hγ1 : γ ≤ 1)
    (hlarge8 : 8 ≤ γ * (Fintype.card V : ℝ))
    (hmin : ∀ i, γ * (Fintype.card V : ℝ) ≤ classSize p i)
    (hsym : ∀ a b, g a b = g b a) (hd : ∀ a, g a a = 0) (hs : EdgeSupported p KQ4 g)
    (hg : ∀ a b, |g a b| ≤ ε) (hcompat : CompatKQ4 p g) 
    (h_PaddedComponents_zeroRowWeightKQ4_symmetric : ∀ {V : Type} [inst : Fintype V] [inst_1 : DecidableEq V] (p : V → Fin 4) (g : V → V → ℝ),
      (∀ (a b : V), g a b = g b a) →
        PartitionedTriangleAbsorption.BlowupB.PaddedFractional.TernarySymmetric
          (PaddedComponents.zeroRowWeightKQ4 p g))
    (h_PaddedComponents_zeroRowWeightKQ4_load : ∀ {V : Type} [inst : Fintype V] [inst_1 : DecidableEq V] (p : V → Fin 4) (g : V → V → ℝ),
      (∀ (a b : V), g a b = g b a) →
        PartitionedTriangleAbsorption.BlowupB.PaddedFractional.ClassRowsZero p g →
          (∀ (a : V), g a a = 0) →
            (∀ (a b : V),
                (¬∃ (k : Fin 4),
                      PartitionedTriangleAbsorption.TypedTransformer.Link PaddedComponents.KQ4 (p a)
                        (p b) k) →
                  g a b = 0) →
              (∀ (i : Fin 4),
                  PartitionedTriangleAbsorption.BlowupB.PaddedFractional.classSize p i ≠ 0) →
                (∀ (i : Fin 4),
                    PartitionedTriangleAbsorption.BlowupB.PaddedFractional.classSize p i - 2 ≠ 0) →
                  (∀ (i : Fin 4),
                      PartitionedTriangleAbsorption.BlowupB.PaddedFractional.classSize p i - 4 ≠ 0) →
                    ∀ (a b : V),
                      PartitionedTriangleAbsorption.BlowupB.PaddedFractional.ternaryLoad
                          (PaddedComponents.zeroRowWeightKQ4 p g) a b =
                        g a b)
    (h_PaddedComponents_vertexWeightKQ4_rows : ∀ {V : Type} [inst : Fintype V] [inst_1 : DecidableEq V] (p : V → Fin 4) (d : V → Fin 4 → ℝ),
      PartitionedTriangleAbsorption.BlowupB.PaddedFractional.VertexDemandZero p d →
        PartitionedTriangleAbsorption.BlowupB.PaddedFractional.VertexDemandSupported p
            PaddedComponents.KQ4 d →
          (∀ (i : Fin 4), PartitionedTriangleAbsorption.BlowupB.PaddedFractional.classSize p i ≠ 0) →
            (∀ (i : Fin 4),
                PartitionedTriangleAbsorption.BlowupB.PaddedFractional.classSize p i - 1 ≠ 0) →
              (∀ (i : Fin 4),
                  PartitionedTriangleAbsorption.BlowupB.PaddedFractional.classSize p i - 2 ≠ 0) →
                (∀ (i : Fin 4),
                    PartitionedTriangleAbsorption.BlowupB.PaddedFractional.classSize p i - 3 ≠ 0) →
                  ∀ (a : V) (k : Fin 4),
                    PartitionedTriangleAbsorption.BlowupB.PaddedFractional.classRow p
                        (PartitionedTriangleAbsorption.BlowupB.PaddedFractional.ternaryLoad
                          (PaddedComponents.vertexWeightKQ4 p d))
                        a k =
                      d a k)
    (h_PaddedComponents_vertexWeightKQ4_symmetric : ∀ {V : Type} [inst : Fintype V] [inst_1 : DecidableEq V] (p : V → Fin 4) (d : V → Fin 4 → ℝ),
      PartitionedTriangleAbsorption.BlowupB.PaddedFractional.TernarySymmetric
        (PaddedComponents.vertexWeightKQ4 p d))
    (h_PaddedComponents_exists_type_correction_KQ4 : ∀ {V : Type} [inst : Fintype V] [DecidableEq V] (p : V → Fin 4) (g : V → V → ℝ) (E δ : ℝ),
      0 ≤ E →
        4 ≤ δ →
          (∀ (i : Fin 4), δ ≤ PartitionedTriangleAbsorption.BlowupB.PaddedFractional.classSize p i) →
            (∀ (a b : V), g a b = g b a) →
              PartitionedTriangleAbsorption.BlowupB.PaddedFractional.EdgeSupported p
                  PaddedComponents.KQ4 g →
                PaddedComponents.CompatKQ4 p g →
                  (∀ (i j : Fin 4),
                      |PartitionedTriangleAbsorption.BlowupB.PaddedFractional.classTotal p g i j| ≤ E) →
                    ∃ (w : V → V → V → ℝ),
                      PartitionedTriangleAbsorption.BlowupB.PaddedFractional.TernarySymmetric w ∧
                        PartitionedTriangleAbsorption.BlowupB.PaddedFractional.TernarySupported p
                            PaddedComponents.KQ4 w ∧
                          PartitionedTriangleAbsorption.BlowupB.PaddedFractional.classTotal p
                                (PartitionedTriangleAbsorption.BlowupB.PaddedFractional.ternaryLoad w) =
                              PartitionedTriangleAbsorption.BlowupB.PaddedFractional.classTotal p g ∧
                            ∀ (a b c : V), |w a b c| ≤ 32 * E / δ ^ 3)
    (h_PaddedComponents_vertexWeightKQ4_supported : ∀ {V : Type} [inst : Fintype V] [inst_1 : DecidableEq V] (p : V → Fin 4) (d : V → Fin 4 → ℝ),
      PartitionedTriangleAbsorption.BlowupB.PaddedFractional.TernarySupported p PaddedComponents.KQ4
        (PaddedComponents.vertexWeightKQ4 p d))
    (h_PaddedComponents_vertexWeightKQ4_bound : ∀ {V : Type} [inst : Fintype V] [inst_1 : DecidableEq V] (p : V → Fin 4) (d : V → Fin 4 → ℝ)
      (D δ : ℝ),
      0 ≤ D →
        4 ≤ δ →
          (∀ (a : V) (j : Fin 4), |d a j| ≤ D) →
            (∀ (i : Fin 4), δ ≤ PartitionedTriangleAbsorption.BlowupB.PaddedFractional.classSize p i) →
              ∀ (a b c : V), |PaddedComponents.vertexWeightKQ4 p d a b c| ≤ 288 * D / δ ^ 2)
    (h_PartitionedTriangleAbsorption_BlowupB_PaddedFractional_complete_inverse_budgets : ∀ (ε γ n : ℝ),
      0 ≤ ε →
        0 < γ →
          γ ≤ 1 →
            0 < n →
              ε + n * (32 * ε / (γ ^ 3 * n)) ≤ 33 * ε / γ ^ 3 ∧
                33 * ε / γ ^ 3 + n * (9504 * ε / (γ ^ 5 * n)) ≤ 9537 * ε / γ ^ 5 ∧
                  32 * ε / (γ ^ 3 * n) + 9504 * ε / (γ ^ 5 * n) + 915552 * ε / (γ ^ 6 * n) ≤
                    2 ^ 20 * ε / (γ ^ 6 * n))
    (h_PartitionedTriangleAbsorption_BlowupB_PaddedFractional_classTotal_bound : ∀ {V : Type} [inst : Fintype V] [DecidableEq V] (p : V → Fin 4) (g : V → V → ℝ) (ε : ℝ),
      0 ≤ ε →
        (∀ (a b : V), |g a b| ≤ ε) →
          ∀ (i j : Fin 4),
            |PartitionedTriangleAbsorption.BlowupB.PaddedFractional.classTotal p g i j| ≤
              ε * (↑(Fintype.card V) : ℝ) ^ 2)
    (h_PartitionedTriangleAbsorption_BlowupB_PaddedFractional_exists_complete_inverse_of_stages : ∀ {V : Type} [inst : Fintype V] [DecidableEq V] (p : V → Fin 4) (F : Finset (Multiset (Fin 4)))
      (g : V → V → ℝ) (ε M0 M1 M2 ε1 ε2 : ℝ),
      0 ≤ ε1 →
        (∀ (a b : V), g a b = g b a) →
          (∀ (a : V), g a a = 0) →
            PartitionedTriangleAbsorption.BlowupB.PaddedFractional.EdgeSupported p F g →
              (∀ (a b : V), |g a b| ≤ ε) →
                ε + (↑(Fintype.card V) : ℝ) * M0 ≤ ε1 →
                  ε1 + (↑(Fintype.card V) : ℝ) * M1 ≤ ε2 →
                    (∃ (w : V → V → V → ℝ),
                        PartitionedTriangleAbsorption.BlowupB.PaddedFractional.TernarySymmetric w ∧
                          PartitionedTriangleAbsorption.BlowupB.PaddedFractional.TernarySupported p F
                              w ∧
                            PartitionedTriangleAbsorption.BlowupB.PaddedFractional.classTotal p
                                  (PartitionedTriangleAbsorption.BlowupB.PaddedFractional.ternaryLoad
                                    w) =
                                PartitionedTriangleAbsorption.BlowupB.PaddedFractional.classTotal p g ∧
                              ∀ (a b c : V), |w a b c| ≤ M0) →
                      (∀ (d : V → Fin 4 → ℝ),
                          PartitionedTriangleAbsorption.BlowupB.PaddedFractional.VertexDemandZero p d →
                            PartitionedTriangleAbsorption.BlowupB.PaddedFractional.VertexDemandSupported
                                p F d →
                              (∀ (a : V) (i : Fin 4), |d a i| ≤ (↑(Fintype.card V) : ℝ) * ε1) →
                                ∃ (w : V → V → V → ℝ),
                                  PartitionedTriangleAbsorption.BlowupB.PaddedFractional.TernarySymmetric
                                      w ∧
                                    PartitionedTriangleAbsorption.BlowupB.PaddedFractional.TernarySupported
                                        p F w ∧
                                      (∀ (a : V) (i : Fin 4),
                                          PartitionedTriangleAbsorption.BlowupB.PaddedFractional.classRow
                                              p
                                              (PartitionedTriangleAbsorption.BlowupB.PaddedFractional.ternaryLoad
                                                w)
                                              a i =
                                            d a i) ∧
                                        ∀ (a b c : V), |w a b c| ≤ M1) →
                        (∀ (f : V → V → ℝ),
                            (∀ (a b : V), f a b = f b a) →
                              (∀ (a : V), f a a = 0) →
                                PartitionedTriangleAbsorption.BlowupB.PaddedFractional.EdgeSupported p F
                                    f →
                                  PartitionedTriangleAbsorption.BlowupB.PaddedFractional.ClassRowsZero p
                                      f →
                                    (∀ (a b : V), |f a b| ≤ ε2) →
                                      ∃ (w : V → V → V → ℝ),
                                        PartitionedTriangleAbsorption.BlowupB.PaddedFractional.TernarySymmetric
                                            w ∧
                                          PartitionedTriangleAbsorption.BlowupB.PaddedFractional.TernarySupported
                                              p F w ∧
                                            (∀ (a b : V),
                                                PartitionedTriangleAbsorption.BlowupB.PaddedFractional.ternaryLoad
                                                    w a b =
                                                  f a b) ∧
                                              ∀ (a b c : V), |w a b c| ≤ M2) →
                          ∃ (w : V → V → V → ℝ),
                            PartitionedTriangleAbsorption.BlowupB.PaddedFractional.TernarySymmetric w ∧
                              PartitionedTriangleAbsorption.BlowupB.PaddedFractional.TernarySupported p
                                  F w ∧
                                (∀ (a b : V),
                                    PartitionedTriangleAbsorption.BlowupB.PaddedFractional.ternaryLoad w
                                        a b =
                                      g a b) ∧
                                  ∀ (a b c : V), |w a b c| ≤ M0 + M1 + M2)
    (h_PaddedComponents_zeroRowWeightKQ4_bound : ∀ {V : Type} [inst : Fintype V] [inst_1 : DecidableEq V] (p : V → Fin 4) (g : V → V → ℝ) (ε δ : ℝ),
      0 ≤ ε →
        8 ≤ δ →
          (∀ (a b : V), |g a b| ≤ ε) →
            (∀ (i : Fin 4), δ ≤ PartitionedTriangleAbsorption.BlowupB.PaddedFractional.classSize p i) →
              ∀ (a b c : V), |PaddedComponents.zeroRowWeightKQ4 p g a b c| ≤ 96 * ε / δ)
    (h_PaddedComponents_zeroRowWeightKQ4_supported : ∀ {V : Type} [inst : Fintype V] [inst_1 : DecidableEq V] (p : V → Fin 4) (g : V → V → ℝ),
      PartitionedTriangleAbsorption.BlowupB.PaddedFractional.TernarySupported p PaddedComponents.KQ4
        (PaddedComponents.zeroRowWeightKQ4 p g))
    :
    ∃ w : V → V → V → ℝ, TernarySymmetric w ∧ TernarySupported p KQ4 w ∧
      (∀ a b, ternaryLoad w a b = g a b) ∧
      ∀ a b c, |w a b c| ≤ (2 : ℝ) ^ 20 * ε / (γ ^ 6 * (Fintype.card V : ℝ)) := by
  have hlarge : 4 ≤ γ * (Fintype.card V : ℝ) := by linarith
  let n : ℝ := Fintype.card V
  have hn : 0 < n := by
    exact (mul_pos_iff_of_pos_left hγ).mp (lt_of_lt_of_le (by norm_num) hlarge)
  have hn0 : n ≠ 0 := ne_of_gt hn
  have hγ0 : γ ≠ 0 := ne_of_gt hγ
  have hε1 : 0 ≤ 33 * ε / γ ^ 3 := by positivity
  have hε2 : 0 ≤ 9537 * ε / γ ^ 5 := by positivity
  have hm (i : Fin 4) : classSize p i ≠ 0 := by have := hmin i; linarith
  have hm1 (i : Fin 4) : classSize p i - 1 ≠ 0 := by have := hmin i; linarith
  have hm2 (i : Fin 4) : classSize p i - 2 ≠ 0 := by have := hmin i; linarith
  have hm3 (i : Fin 4) : classSize p i - 3 ≠ 0 := by have := hmin i; linarith
  have hm4 (i : Fin 4) : classSize p i - 4 ≠ 0 := by have := hmin i; linarith
  obtain ⟨hstep1, hstep2, hbudget⟩ := h_PartitionedTriangleAbsorption_BlowupB_PaddedFractional_complete_inverse_budgets ε γ n hε hγ hγ1 hn
  have he0 : 32 * (ε * n ^ 2) / (γ * n) ^ 3 = 32 * ε / (γ ^ 3 * n) := by
    field_simp [hγ0, hn0]
  have he1 : 288 * (n * (33 * ε / γ ^ 3)) / (γ * n) ^ 2 =
      9504 * ε / (γ ^ 5 * n) := by
    field_simp [hγ0, hn0]
    ring
  have he2 : 96 * (9537 * ε / γ ^ 5) / (γ * n) = 915552 * ε / (γ ^ 6 * n) := by
    field_simp [hγ0, hn0]
    ring
  have hstage : ∃ w : V → V → V → ℝ,
      TernarySymmetric w ∧ TernarySupported p KQ4 w ∧ (∀ a b, ternaryLoad w a b = g a b) ∧
      ∀ a b c, |w a b c| ≤
        32 * ε / (γ ^ 3 * n) + 9504 * ε / (γ ^ 5 * n) + 915552 * ε / (γ ^ 6 * n) := by
    apply h_PartitionedTriangleAbsorption_BlowupB_PaddedFractional_exists_complete_inverse_of_stages p KQ4 g ε _ _ _
      (33 * ε / γ ^ 3) (9537 * ε / γ ^ 5) hε1 hsym hd hs hg hstep1 hstep2
    · obtain ⟨w, hsw, htw, hew, hbw⟩ := h_PaddedComponents_exists_type_correction_KQ4 p g (ε * n ^ 2)
        (γ * n) (by positivity) hlarge hmin hsym hs hcompat (h_PartitionedTriangleAbsorption_BlowupB_PaddedFractional_classTotal_bound p g ε hε hg)
      exact ⟨w, hsw, htw, hew, fun a b c => he0 ▸ hbw a b c⟩
    · intro d hz hds hdb
      refine ⟨vertexWeightKQ4 p d, h_PaddedComponents_vertexWeightKQ4_symmetric p d,
        h_PaddedComponents_vertexWeightKQ4_supported p d, h_PaddedComponents_vertexWeightKQ4_rows p d hz hds hm hm1 hm2 hm3, ?_⟩
      intro a b c
      exact he1 ▸ h_PaddedComponents_vertexWeightKQ4_bound p d (n * (33 * ε / γ ^ 3)) (γ * n)
        (by positivity) hlarge hdb hmin a b c
    · intro f hf hfd hfs hr hb
      refine ⟨zeroRowWeightKQ4 p f, h_PaddedComponents_zeroRowWeightKQ4_symmetric p f hf,
        h_PaddedComponents_zeroRowWeightKQ4_supported p f,
        h_PaddedComponents_zeroRowWeightKQ4_load p f hf hr hfd hfs hm hm2 hm4, ?_⟩
      intro a b c
      exact he2 ▸ h_PaddedComponents_zeroRowWeightKQ4_bound p f (9537 * ε / γ ^ 5) (γ * n)
        hε2 hlarge8 hb hmin a b c
  obtain ⟨w, hsw, htw, hew, hbw⟩ := hstage
  exact ⟨w, hsw, htw, hew, fun a b c => (hbw a b c).trans hbudget⟩

end PaddedComponents
