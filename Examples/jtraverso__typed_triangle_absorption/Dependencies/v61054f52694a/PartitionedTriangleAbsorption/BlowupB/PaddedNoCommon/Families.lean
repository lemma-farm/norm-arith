/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import Examples.jtraverso__typed_triangle_absorption.Dependencies.v61054f52694a.PartitionedTriangleAbsorption.BlowupB.PaddedNoCommon.LatticeFrame
@[expose] public section
/-!
# The fourteen connected trivial-lattice families without common neighbour classes

`CENSUS_THREESTEP_NOCOMMON_20261013.md` (Python census) lists 14 `S₄`-classes with
`ThreeStepLinks`, a connected allowed-pair graph, a trivial lattice and no common neighbour classes.
They are `NC1`, …, `NC14` below, in the order of the census table. Each contains one of six
minimal base families `FnA`, …, `FnF` with the SAME allowed pairs:

| base | types | allowed pairs | census rows |
|---|---|---|---|
| `FnA` | 000 001 002 011 111 113 | 00 01 02 11 13 | NC1 |
| `FnB` | 000 001 002 011 113 133 | 00 01 02 11 13 33 | NC2, NC5 |
| `FnC` | 000 001 002 011 022 111 113 | 00 01 02 11 13 22 | NC3, NC9 |
| `FnD` | 000 001 002 011 022 113 133 | 00 01 02 11 13 22 33 | NC4, NC7, NC8, NC12, NC14 |
| `FnE` | 000 001 011 112 122 223 233 | 00 01 11 12 22 23 33 | NC6, NC11 |
| `FnF` | 000 001 002 011 022 111 223 233 | 00 01 02 11 22 23 33 | NC10, NC13 |

All finite facts here (card three, `ThreeStepLinks`, `Walk4`, a forbidden partner for every class,
inclusion and equality of allowed pairs) are checked by `decide`. The facts that the lattice is
trivial and that there are no common neighbour classes are NOT used as census input: the lattice is
proved in `PaddedNoCommon/Lattice.lean`, and the absence of common neighbours is only recorded
(`not_common_*`).
-/
namespace PaddedNoCommon
open Finset PartitionedTriangleAbsorption
open PartitionedTriangleAbsorption.TypedTransformer
open PaddedGeneral
/-- Base family `FnA`. -/
noncomputable def FnA : Finset (Multiset (Fin 4)) :=
  {{0, 0, 0}, {0, 0, 1}, {0, 0, 2}, {0, 1, 1}, {1, 1, 1}, {1, 1, 3}}
/-- Base family `FnB`. -/
noncomputable def FnB : Finset (Multiset (Fin 4)) :=
  {{0, 0, 0}, {0, 0, 1}, {0, 0, 2}, {0, 1, 1}, {1, 1, 3}, {1, 3, 3}}
/-- Base family `FnC`. -/
noncomputable def FnC : Finset (Multiset (Fin 4)) :=
  {{0, 0, 0}, {0, 0, 1}, {0, 0, 2}, {0, 1, 1}, {0, 2, 2}, {1, 1, 1}, {1, 1, 3}}
/-- Base family `FnD`. -/
noncomputable def FnD : Finset (Multiset (Fin 4)) :=
  {{0, 0, 0}, {0, 0, 1}, {0, 0, 2}, {0, 1, 1}, {0, 2, 2}, {1, 1, 3}, {1, 3, 3}}
/-- Base family `FnE`. -/
noncomputable def FnE : Finset (Multiset (Fin 4)) :=
  {{0, 0, 0}, {0, 0, 1}, {0, 1, 1}, {1, 1, 2}, {1, 2, 2}, {2, 2, 3}, {2, 3, 3}}
/-- Base family `FnF`. -/
noncomputable def FnF : Finset (Multiset (Fin 4)) :=
  {{0, 0, 0}, {0, 0, 1}, {0, 0, 2}, {0, 1, 1}, {0, 2, 2}, {1, 1, 1}, {2, 2, 3}, {2, 3, 3}}
structure BaseFacts (F : Finset (Multiset (Fin 4))) : Prop where
  card : ∀ τ ∈ F, Multiset.card τ = 3
  three : ThreeStepLinks F
  walk : Walk4 (fun i j : Fin 4 => ∃ k, Link F i j k)
  facts : FamilyFacts F
/-- A census family over a base: same allowed pairs, more types. -/
structure OverBase (F0 F : Finset (Multiset (Fin 4))) : Prop where
  sub : F0 ⊆ F
  allowed : ∀ i j : Fin 4, (∃ k, Link F i j k) ↔ (∃ k, Link F0 i j k)
  facts : FamilyFacts F
theorem baseFacts_FnA : BaseFacts FnA where
  card := by unfold FnA; decide
  three := by unfold ThreeStepLinks Link FnA; decide
  walk := by unfold Walk4; beta_reduce; unfold Link FnA; decide
  facts := ⟨by unfold FnA; decide, by unfold Link FnA; decide,
    by intro i; fin_cases i <;> (unfold Link FnA; decide)⟩
theorem baseFacts_FnB : BaseFacts FnB where
  card := by unfold FnB; decide
  three := by unfold ThreeStepLinks Link FnB; decide
  walk := by unfold Walk4; beta_reduce; unfold Link FnB; decide
  facts := ⟨by unfold FnB; decide, by unfold Link FnB; decide,
    by intro i; fin_cases i <;> (unfold Link FnB; decide)⟩
theorem baseFacts_FnC : BaseFacts FnC where
  card := by unfold FnC; decide
  three := by unfold ThreeStepLinks Link FnC; decide
  walk := by unfold Walk4; beta_reduce; unfold Link FnC; decide
  facts := ⟨by unfold FnC; decide, by unfold Link FnC; decide,
    by intro i; fin_cases i <;> (unfold Link FnC; decide)⟩
theorem baseFacts_FnD : BaseFacts FnD where
  card := by unfold FnD; decide
  three := by unfold ThreeStepLinks Link FnD; decide
  walk := by unfold Walk4; beta_reduce; unfold Link FnD; decide
  facts := ⟨by unfold FnD; decide, by unfold Link FnD; decide,
    by intro i; fin_cases i <;> (unfold Link FnD; decide)⟩
theorem baseFacts_FnE : BaseFacts FnE where
  card := by unfold FnE; decide
  three := by unfold ThreeStepLinks Link FnE; decide
  walk := by unfold Walk4; beta_reduce; unfold Link FnE; decide
  facts := ⟨by unfold FnE; decide, by unfold Link FnE; decide,
    by intro i; fin_cases i <;> (unfold Link FnE; decide)⟩
theorem baseFacts_FnF : BaseFacts FnF where
  card := by unfold FnF; decide
  three := by unfold ThreeStepLinks Link FnF; decide
  walk := by unfold Walk4; beta_reduce; unfold Link FnF; decide
  facts := ⟨by unfold FnF; decide, by unfold Link FnF; decide,
    by intro i; fin_cases i <;> (unfold Link FnF; decide)⟩
end PaddedNoCommon
