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
def TernarySymmetric (w : V → V → V → ℝ) : Prop :=
  (∀ a b c, w a b c = w b a c) ∧ (∀ a b c, w a b c = w a c b)
def TernarySupported (p : V → Fin t) (F : Finset (Multiset (Fin t)))
    (w : V → V → V → ℝ) : Prop :=
  ∀ a b c, ¬ AdmissibleTriple p F a b c → w a b c = 0
def ternaryLoad [Fintype V] (w : V → V → V → ℝ) (a b : V) : ℝ := ∑ c, w a b c

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

-- ==== Examples.jtraverso__typed_triangle_absorption.Dependencies.v917af0cf750a.PartitionedTriangleAbsorption.BlowupB.PaddedFractional.PhysicalVertexModes ====
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

-- ==== Examples.jtraverso__typed_triangle_absorption.Dependencies.v917af0cf750a.PartitionedTriangleAbsorption.BlowupB.PaddedF12.TypeInverse ====
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

-- ==== Examples.jtraverso__typed_triangle_absorption.Examples.Example_fd03c31303790ef40ce1_InverseKQ4 ====
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
def realMatrixKQ4 (t00 t01 t02 t11 t12 t33 : ℝ) : Fin 4 → Fin 4 → ℝ :=
  ![![t00, t01, t02, 0], ![t01, t11, t12, 0], ![t02, t12, 0, 0], ![0, 0, 0, t33]]

def typeWeightKQ4 (p : V → Fin 4) (z001 z002 z011 z012 z333 : ℝ) (a b c : V) : ℝ :=
  repeatedTypeWeight p 0 1 z001 a b c +
  repeatedTypeWeight p 0 2 z002 a b c +
  repeatedTypeWeight p 1 0 z011 a b c +
  tripartiteTypeWeight p 0 1 2 z012 a b c +
  monoTypeWeight p 3 z333 a b c

/-- The real compatibility of `KQ4` on class totals (the charge vanishes on the totals). -/
def CompatKQ4 (p : V → Fin 4) (g : V → V → ℝ) : Prop :=
  (1 : ℝ) * classTotal p g 0 0 + (-1 : ℝ) * classTotal p g 0 1 + (-1 : ℝ) * classTotal p g 0 2 + (1 : ℝ) * classTotal p g 1 1 + (2 : ℝ) * classTotal p g 1 2 = 0
set_option linter.unusedVariables false in
theorem exists_type_correction_KQ4 (p : V → Fin 4) (g : V → V → ℝ) (E δ : ℝ)
    (hE : 0 ≤ E) (hδ : 4 ≤ δ) (hm : ∀ i, δ ≤ classSize p i)
    (hsym : ∀ a b, g a b = g b a) (hs : EdgeSupported p KQ4 g)
    (hcompat : CompatKQ4 p g)
    (hbound : ∀ i j, |classTotal p g i j| ≤ E) 
    (h_PaddedComponents_typeWeightKQ4_totals : ∀ {V : Type u_1} [inst : Fintype V] [inst_1 : DecidableEq V] (p : V → Fin 4)
      (z001 z002 z011 z012 z333 : ℝ),
      (∀ (i : Fin 4), PartitionedTriangleAbsorption.BlowupB.PaddedFractional.classSize p i ≠ 0) →
        (∀ (i : Fin 4), PartitionedTriangleAbsorption.BlowupB.PaddedFractional.classSize p i - 1 ≠ 0) →
          (∀ (i : Fin 4),
              PartitionedTriangleAbsorption.BlowupB.PaddedFractional.classSize p i - 2 ≠ 0) →
            PartitionedTriangleAbsorption.BlowupB.PaddedFractional.classTotal p
                (PartitionedTriangleAbsorption.BlowupB.PaddedFractional.ternaryLoad
                  (PaddedComponents.typeWeightKQ4 p z001 z002 z011 z012 z333)) =
              PaddedComponents.realMatrixKQ4 (2 * z001 + 2 * z002) (2 * z001 + 2 * z011 + 1 * z012)
                (2 * z002 + 1 * z012) (2 * z011) (1 * z012) (6 * z333))
    (h_PaddedComponents_typeWeightKQ4_symmetric : ∀ {V : Type u_1} [inst : Fintype V] [inst_1 : DecidableEq V] (p : V → Fin 4)
      (z001 z002 z011 z012 z333 : ℝ),
      PartitionedTriangleAbsorption.BlowupB.PaddedFractional.TernarySymmetric
        (PaddedComponents.typeWeightKQ4 p z001 z002 z011 z012 z333))
    (h_PaddedComponents_typeWeightKQ4_bound : ∀ {V : Type u_1} [inst : Fintype V] [inst_1 : DecidableEq V] (p : V → Fin 4)
      (z001 z002 z011 z012 z333 E δ : ℝ),
      0 ≤ E →
        4 ≤ δ →
          |z001| ≤ 8 * E →
            |z002| ≤ 8 * E →
              |z011| ≤ 8 * E →
                |z012| ≤ 8 * E →
                  |z333| ≤ 2 * E →
                    (∀ (i : Fin 4),
                        δ ≤ PartitionedTriangleAbsorption.BlowupB.PaddedFractional.classSize p i) →
                      ∀ (a b c : V),
                        |PaddedComponents.typeWeightKQ4 p z001 z002 z011 z012 z333 a b c| ≤
                          32 * E / δ ^ 3)
    (h_PaddedComponents_typeWeightKQ4_supported : ∀ {V : Type u_1} [inst : Fintype V] [inst_1 : DecidableEq V] (p : V → Fin 4)
      (z001 z002 z011 z012 z333 : ℝ),
      PartitionedTriangleAbsorption.BlowupB.PaddedFractional.TernarySupported p PaddedComponents.KQ4
        (PaddedComponents.typeWeightKQ4 p z001 z002 z011 z012 z333))
    (h_PaddedComponents_classTotal_realMatrixKQ4 : ∀ {V : Type u_1} [inst : Fintype V] [DecidableEq V] (p : V → Fin 4) (g : V → V → ℝ),
      (∀ (a b : V), g a b = g b a) →
        PartitionedTriangleAbsorption.BlowupB.PaddedFractional.EdgeSupported p PaddedComponents.KQ4 g →
          PartitionedTriangleAbsorption.BlowupB.PaddedFractional.classTotal p g =
            PaddedComponents.realMatrixKQ4
              (PartitionedTriangleAbsorption.BlowupB.PaddedFractional.classTotal p g 0 0)
              (PartitionedTriangleAbsorption.BlowupB.PaddedFractional.classTotal p g 0 1)
              (PartitionedTriangleAbsorption.BlowupB.PaddedFractional.classTotal p g 0 2)
              (PartitionedTriangleAbsorption.BlowupB.PaddedFractional.classTotal p g 1 1)
              (PartitionedTriangleAbsorption.BlowupB.PaddedFractional.classTotal p g 1 2)
              (PartitionedTriangleAbsorption.BlowupB.PaddedFractional.classTotal p g 3 3))
    :
    ∃ w : V → V → V → ℝ,
      TernarySymmetric w ∧ TernarySupported p KQ4 w ∧
      classTotal p (ternaryLoad w) = classTotal p g ∧
      ∀ a b c, |w a b c| ≤ 32 * E / δ ^ 3 := by
  unfold CompatKQ4 at hcompat
  have b00 := abs_le.mp (hbound 0 0)
  have b01 := abs_le.mp (hbound 0 1)
  have b02 := abs_le.mp (hbound 0 2)
  have b11 := abs_le.mp (hbound 1 1)
  have b12 := abs_le.mp (hbound 1 2)
  have b33 := abs_le.mp (hbound 3 3)
  let z001 : ℝ := (1 / 2) * classTotal p g 0 0 + (-1 / 2) * classTotal p g 0 2 + (1 / 2) * classTotal p g 1 2
  let z002 : ℝ := (1 / 2) * classTotal p g 0 2 + (-1 / 2) * classTotal p g 1 2
  let z011 : ℝ := (1 / 2) * classTotal p g 1 1
  let z012 : ℝ := 1 * classTotal p g 1 2
  let z333 : ℝ := (1 / 6) * classTotal p g 3 3
  have hz001 : |z001| ≤ 8 * E := by
    apply abs_le.mpr; constructor <;> dsimp only [z001] <;>
      linarith [b00.1, b00.2, b01.1, b01.2, b02.1, b02.2, b11.1, b11.2, b12.1, b12.2, b33.1, b33.2]
  have hz002 : |z002| ≤ 8 * E := by
    apply abs_le.mpr; constructor <;> dsimp only [z002] <;>
      linarith [b00.1, b00.2, b01.1, b01.2, b02.1, b02.2, b11.1, b11.2, b12.1, b12.2, b33.1, b33.2]
  have hz011 : |z011| ≤ 8 * E := by
    apply abs_le.mpr; constructor <;> dsimp only [z011] <;>
      linarith [b00.1, b00.2, b01.1, b01.2, b02.1, b02.2, b11.1, b11.2, b12.1, b12.2, b33.1, b33.2]
  have hz012 : |z012| ≤ 8 * E := by
    apply abs_le.mpr; constructor <;> dsimp only [z012] <;>
      linarith [b00.1, b00.2, b01.1, b01.2, b02.1, b02.2, b11.1, b11.2, b12.1, b12.2, b33.1, b33.2]
  have hz333 : |z333| ≤ 2 * E := by
    apply abs_le.mpr; constructor <;> dsimp only [z333] <;>
      linarith [b00.1, b00.2, b01.1, b01.2, b02.1, b02.2, b11.1, b11.2, b12.1, b12.2, b33.1, b33.2]
  have hn (i : Fin 4) : classSize p i ≠ 0 := by have := hm i; linarith
  have hn1 (i : Fin 4) : classSize p i - 1 ≠ 0 := by have := hm i; linarith
  have hn2 (i : Fin 4) : classSize p i - 2 ≠ 0 := by have := hm i; linarith
  refine ⟨typeWeightKQ4 p z001 z002 z011 z012 z333, h_PaddedComponents_typeWeightKQ4_symmetric p _ _ _ _ _,
    h_PaddedComponents_typeWeightKQ4_supported p _ _ _ _ _, ?_,
    h_PaddedComponents_typeWeightKQ4_bound p _ _ _ _ _ E δ hE hδ hz001 hz002 hz011 hz012 hz333 hm⟩
  rw [h_PaddedComponents_typeWeightKQ4_totals p _ _ _ _ _ hn hn1 hn2, h_PaddedComponents_classTotal_realMatrixKQ4 p g hsym hs]
  congr 1 <;> dsimp only [z001, z002, z011, z012, z333] <;> linarith

end PaddedComponents
