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
public import Mathlib.Probability.Independence.Basic
public import Mathlib.Probability.Distributions.Bernoulli
public import Mathlib.Probability.Moments.SubGaussian
public import Mathlib.Analysis.SpecialFunctions.Exponential
public import Mathlib.Analysis.Complex.ExponentialBounds
public import Mathlib.Combinatorics.SimpleGraph.DegreeSum
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.Algebra.Order.Ring.Abs
public import Mathlib.Combinatorics.SimpleGraph.CompleteMultipartite
public import Mathlib.Algebra.Order.Floor.Semiring
public import Mathlib.Algebra.Module.BigOperators
public import Mathlib.Data.Int.Interval
public import Mathlib.Logic.Equiv.Basic
public import Mathlib.Order.Interval.Finset.Nat

-- ==== Examples.jtraverso__typed_triangle_absorption.Dependencies.v61054f52694a.PartitionedTriangleAbsorption.BlowupB.PaddedFractional.PhysicalEdgeModes ====
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

-- ==== Examples.jtraverso__typed_triangle_absorption.Dependencies.v61054f52694a.PartitionedTriangleAbsorption.BlowupB.PaddedFractional.PhysicalVertexModes ====
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
open Finset 
variable {V : Type*} {t : ℕ} [Fintype V] [DecidableEq V]

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

-- ==== Examples.jtraverso__typed_triangle_absorption.Dependencies.v61054f52694a.PartitionedTriangleAbsorption.BlowupB.PaddedFractional.PhysicalTypeModes ====
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

end PartitionedTriangleAbsorption.BlowupB.PaddedFractional

end
end
end

-- ==== Examples.jtraverso__typed_triangle_absorption.Dependencies.v61054f52694a.PartitionedTriangleAbsorption.BlowupB.PaddedFstar.Inverse ====
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
end PaddedFstar

end
end
end

-- ==== Examples.jtraverso__typed_triangle_absorption.Dependencies.v61054f52694a.PartitionedTriangleAbsorption.BlowupB.PaddedNoCommon.InverseFrame ====
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



open PartitionedTriangleAbsorption.BlowupB.PaddedFractional


variable {V : Type*} [Fintype V] [DecidableEq V]
/-- A linear combination of the four row demands of a vertex. -/
def lc (d : V → Fin 4 → ℝ) (a0 a1 a2 a3 : ℝ) (v : V) : ℝ :=
  a0 * d v 0 + a1 * d v 1 + a2 * d v 2 + a3 * d v 3

end PaddedNoCommon

end
end
end

-- ==== Examples.jtraverso__typed_triangle_absorption.Examples.Example_857602e4c67f6c86f0d0_Inv63 ====
/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
@[expose] public section
/-! # `CompleteInverseCert₈` for PAR families (generated by `gen_inv_par.py`, frame of `gen_km.py`) -/
noncomputable section
namespace PaddedComponents
open Finset PartitionedTriangleAbsorption



open PartitionedTriangleAbsorption.BlowupB.PaddedFractional

open PaddedFstar PaddedNoCommon 

variable {V : Type*} [Fintype V] [DecidableEq V]
set_option linter.unusedSectionVars false
set_option maxHeartbeats 8000000

def typeWeightF_PAR504 (p : V → Fin 4) (z000 z001 z002 z011 z022 z133 z233 z333 : ℝ) (a b c : V) : ℝ :=
  monoTypeWeight p 0 z000 a b c +
  repeatedTypeWeight p 0 1 z001 a b c +
  repeatedTypeWeight p 0 2 z002 a b c +
  repeatedTypeWeight p 1 0 z011 a b c +
  repeatedTypeWeight p 2 0 z022 a b c +
  repeatedTypeWeight p 3 1 z133 a b c +
  repeatedTypeWeight p 3 2 z233 a b c +
  monoTypeWeight p 3 z333 a b c

def vertexWeightF_PAR504 (p : V → Fin 4) (d : V → Fin 4 → ℝ) (a b c : V) : ℝ :=
  repeatedVertexWeight p 0 1 (lc d 1 0 0 0) a b c +
  singletonVertexWeight p 1 0 (lc d (-1 / 2) (1 / 2) 0 0) a b c +
  singletonVertexWeight p 2 0 (lc d 0 0 (1 / 2) 0) a b c +
  singletonVertexWeight p 0 1 (lc d (1 / 2) (-1 / 2) 0 0) a b c +
  repeatedVertexWeight p 1 0 (lc d 0 1 0 0) a b c +
  singletonVertexWeight p 3 1 (lc d 0 0 0 (1 / 2)) a b c +
  singletonVertexWeight p 0 2 (lc d (1 / 2) 0 (-1 / 2) 0) a b c +
  repeatedVertexWeight p 2 0 (lc d 0 0 1 0) a b c +
  singletonVertexWeight p 3 2 (lc d 0 0 0 (1 / 2)) a b c +
  singletonVertexWeight p 1 3 (lc d 0 (1 / 2) (1 / 2) (-1 / 2)) a b c +
  repeatedVertexWeight p 3 1 (lc d 0 0 (-1) 1) a b c +
  repeatedVertexWeight p 3 2 (lc d 0 0 1 0) a b c


set_option linter.unusedVariables false in
theorem vertexWeightF_PAR504_bound (p : V → Fin 4) (d : V → Fin 4 → ℝ) (D δ : ℝ)
    (hD : 0 ≤ D) (hδ : 4 ≤ δ) (hd : ∀ a j, |d a j| ≤ D)
    (hm : ∀ i, δ ≤ classSize p i) (a b c : V) 
    (h_PaddedNoCommon_lc_bound : ∀ {V : Type u_1} [Fintype V] [DecidableEq V] (d : V → Fin 4 → ℝ) (D : ℝ),
      (∀ (a : V) (j : Fin 4), |d a j| ≤ D) →
        ∀ (a0 a1 a2 a3 : ℝ) (v : V),
          |PaddedNoCommon.lc d a0 a1 a2 a3 v| ≤ (|a0| + |a1| + |a2| + |a3|) * D)
    (h_PartitionedTriangleAbsorption_BlowupB_PaddedFractional_vertexMode_bounds : ∀ {V : Type u_1} {t : ℕ} [inst : Fintype V] [inst_1 : DecidableEq V] (p : V → Fin t) (f : V → ℝ)
      (D δ : ℝ),
      0 ≤ D →
        4 ≤ δ →
          (∀ (a : V), |f a| ≤ D) →
            (∀ (i : Fin t), δ ≤ PartitionedTriangleAbsorption.BlowupB.PaddedFractional.classSize p i) →
              ∀ (a b c : V),
                (∀ (i j : Fin t),
                    |PartitionedTriangleAbsorption.BlowupB.PaddedFractional.repeatedVertexWeight p i j f
                          a b c| ≤
                      12 * D / δ ^ 2) ∧
                  (∀ (i j : Fin t),
                      |PartitionedTriangleAbsorption.BlowupB.PaddedFractional.singletonVertexWeight p i
                            j f a b c| ≤
                        12 * D / δ ^ 2) ∧
                    ∀ (i j k : Fin t),
                      |PartitionedTriangleAbsorption.BlowupB.PaddedFractional.tripartiteVertexWeight p i
                            j k f a b c| ≤
                        12 * D / δ ^ 2)
    :
    |vertexWeightF_PAR504 p d a b c| ≤ 288 * D / δ ^ 2 := by
  have hf (a0 a1 a2 a3 m : ℝ) (hm0 : |a0| + |a1| + |a2| + |a3| ≤ m) (v : V) :
      |lc d a0 a1 a2 a3 v| ≤ m * D :=
    (h_PaddedNoCommon_lc_bound d D hd a0 a1 a2 a3 v).trans (mul_le_mul_of_nonneg_right hm0 hD)
  have e0 := (h_PartitionedTriangleAbsorption_BlowupB_PaddedFractional_vertexMode_bounds p (lc d 1 0 0 0) (1 * D) δ (mul_nonneg (by norm_num : (0 : ℝ) ≤ 1) hD) hδ (hf 1 0 0 0 1 (by norm_num)) hm a b c).1 0 1
  rw [show 12 * (1 * D) / δ ^ 2 = (12 * 1) * (D / δ ^ 2) by ring] at e0
  have e1 := (h_PartitionedTriangleAbsorption_BlowupB_PaddedFractional_vertexMode_bounds p (lc d (-1 / 2) (1 / 2) 0 0) (1 * D) δ (mul_nonneg (by norm_num : (0 : ℝ) ≤ 1) hD) hδ (hf (-1 / 2) (1 / 2) 0 0 1 (by norm_num)) hm a b c).2.1 1 0
  rw [show 12 * (1 * D) / δ ^ 2 = (12 * 1) * (D / δ ^ 2) by ring] at e1
  have e2 := (h_PartitionedTriangleAbsorption_BlowupB_PaddedFractional_vertexMode_bounds p (lc d 0 0 (1 / 2) 0) ((1 / 2) * D) δ (mul_nonneg (by norm_num : (0 : ℝ) ≤ (1 / 2)) hD) hδ (hf 0 0 (1 / 2) 0 (1 / 2) (by norm_num)) hm a b c).2.1 2 0
  rw [show 12 * ((1 / 2) * D) / δ ^ 2 = (12 * (1 / 2)) * (D / δ ^ 2) by ring] at e2
  have e3 := (h_PartitionedTriangleAbsorption_BlowupB_PaddedFractional_vertexMode_bounds p (lc d (1 / 2) (-1 / 2) 0 0) (1 * D) δ (mul_nonneg (by norm_num : (0 : ℝ) ≤ 1) hD) hδ (hf (1 / 2) (-1 / 2) 0 0 1 (by norm_num)) hm a b c).2.1 0 1
  rw [show 12 * (1 * D) / δ ^ 2 = (12 * 1) * (D / δ ^ 2) by ring] at e3
  have e4 := (h_PartitionedTriangleAbsorption_BlowupB_PaddedFractional_vertexMode_bounds p (lc d 0 1 0 0) (1 * D) δ (mul_nonneg (by norm_num : (0 : ℝ) ≤ 1) hD) hδ (hf 0 1 0 0 1 (by norm_num)) hm a b c).1 1 0
  rw [show 12 * (1 * D) / δ ^ 2 = (12 * 1) * (D / δ ^ 2) by ring] at e4
  have e5 := (h_PartitionedTriangleAbsorption_BlowupB_PaddedFractional_vertexMode_bounds p (lc d 0 0 0 (1 / 2)) ((1 / 2) * D) δ (mul_nonneg (by norm_num : (0 : ℝ) ≤ (1 / 2)) hD) hδ (hf 0 0 0 (1 / 2) (1 / 2) (by norm_num)) hm a b c).2.1 3 1
  rw [show 12 * ((1 / 2) * D) / δ ^ 2 = (12 * (1 / 2)) * (D / δ ^ 2) by ring] at e5
  have e6 := (h_PartitionedTriangleAbsorption_BlowupB_PaddedFractional_vertexMode_bounds p (lc d (1 / 2) 0 (-1 / 2) 0) (1 * D) δ (mul_nonneg (by norm_num : (0 : ℝ) ≤ 1) hD) hδ (hf (1 / 2) 0 (-1 / 2) 0 1 (by norm_num)) hm a b c).2.1 0 2
  rw [show 12 * (1 * D) / δ ^ 2 = (12 * 1) * (D / δ ^ 2) by ring] at e6
  have e7 := (h_PartitionedTriangleAbsorption_BlowupB_PaddedFractional_vertexMode_bounds p (lc d 0 0 1 0) (1 * D) δ (mul_nonneg (by norm_num : (0 : ℝ) ≤ 1) hD) hδ (hf 0 0 1 0 1 (by norm_num)) hm a b c).1 2 0
  rw [show 12 * (1 * D) / δ ^ 2 = (12 * 1) * (D / δ ^ 2) by ring] at e7
  have e8 := (h_PartitionedTriangleAbsorption_BlowupB_PaddedFractional_vertexMode_bounds p (lc d 0 0 0 (1 / 2)) ((1 / 2) * D) δ (mul_nonneg (by norm_num : (0 : ℝ) ≤ (1 / 2)) hD) hδ (hf 0 0 0 (1 / 2) (1 / 2) (by norm_num)) hm a b c).2.1 3 2
  rw [show 12 * ((1 / 2) * D) / δ ^ 2 = (12 * (1 / 2)) * (D / δ ^ 2) by ring] at e8
  have e9 := (h_PartitionedTriangleAbsorption_BlowupB_PaddedFractional_vertexMode_bounds p (lc d 0 (1 / 2) (1 / 2) (-1 / 2)) ((3 / 2) * D) δ (mul_nonneg (by norm_num : (0 : ℝ) ≤ (3 / 2)) hD) hδ (hf 0 (1 / 2) (1 / 2) (-1 / 2) (3 / 2) (by norm_num)) hm a b c).2.1 1 3
  rw [show 12 * ((3 / 2) * D) / δ ^ 2 = (12 * (3 / 2)) * (D / δ ^ 2) by ring] at e9
  have e10 := (h_PartitionedTriangleAbsorption_BlowupB_PaddedFractional_vertexMode_bounds p (lc d 0 0 (-1) 1) (2 * D) δ (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hD) hδ (hf 0 0 (-1) 1 2 (by norm_num)) hm a b c).1 3 1
  rw [show 12 * (2 * D) / δ ^ 2 = (12 * 2) * (D / δ ^ 2) by ring] at e10
  have e11 := (h_PartitionedTriangleAbsorption_BlowupB_PaddedFractional_vertexMode_bounds p (lc d 0 0 1 0) (1 * D) δ (mul_nonneg (by norm_num : (0 : ℝ) ≤ 1) hD) hδ (hf 0 0 1 0 1 (by norm_num)) hm a b c).1 3 2
  rw [show 12 * (1 * D) / δ ^ 2 = (12 * 1) * (D / δ ^ 2) by ring] at e11
  have hM0 : 0 ≤ D / δ ^ 2 := by positivity
  unfold vertexWeightF_PAR504
  rw [show 288 * D / δ ^ 2 = 288 * (D / δ ^ 2) by ring]
  generalize D / δ ^ 2 = M at e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 hM0 ⊢
  rw [abs_le] at e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 ⊢
  constructor <;> linarith [e0.1, e0.2, e1.1, e1.2, e2.1, e2.2, e3.1, e3.2, e4.1, e4.2, e5.1, e5.2, e6.1, e6.2, e7.1, e7.2, e8.1, e8.2, e9.1, e9.2, e10.1, e10.2, e11.1, e11.2]

end PaddedComponents
