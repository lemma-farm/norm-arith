/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import Examples.jtraverso__typed_triangle_absorption.Dependencies.v61054f52694a.PartitionedTriangleAbsorption.SignedHinge.Groups
/-! # The occurrence gadget: one hinge between a certificate triangle and a fresh triangle

Let `t = {a,b,c}` be a typed triangle and `x` a further vertex, and let `H` be a hinge for the
two copies `{a,b,c}` and `{a,b,x}` (sharing exactly the edge `ab`). Fix a decomposition of
`H ∪ {ac, bc}` and let `{a,c,y}`, `{b,c,z}` be its triangles through `ac` and `bc`. Then

* `y, z` are new vertices (`∉ {a,b,c,x}`), `y ≠ z`;
* the *slot wedges* `{ax,bx}`, `{ay,cy}`, `{bz,cz}` close the three edges of `t` with the
  apices `x, y, z` (slot triangles `{a,b,x}`, `{a,c,y}`, `{b,c,z}`);
* `R = H ∪ {ax,bx}` is decomposable (first hinge mode), and
  `Y = H \ {ay,cy,bz,cz}` is decomposable (rest of the second hinge mode);
* `R` is the disjoint union of `Y` and the three slot wedges (the "hexagon").

Hence `Y` is a decomposable absorber for the hexagon `{ax,bx,ay,cy,bz,cz}` which uses **no**
edge of `t`: this is the root-clean local closure used for every certificate occurrence.
Generic in the type family `F`.
-/
@[expose] public section
namespace PartitionedTriangleAbsorption.SignedHinge
open Finset
variable {V : Type*} [DecidableEq V] {t : ℕ} {p : V → Fin t} {F : Finset (Multiset (Fin t))}
end PartitionedTriangleAbsorption.SignedHinge
