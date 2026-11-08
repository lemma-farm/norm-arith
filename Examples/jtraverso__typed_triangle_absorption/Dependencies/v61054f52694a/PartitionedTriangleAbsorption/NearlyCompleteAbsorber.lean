/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import Examples.jtraverso__typed_triangle_absorption.Dependencies.v61054f52694a.PartitionedTriangleAbsorption.BlowupB.Nearly
public import Examples.jtraverso__typed_triangle_absorption.Dependencies.v61054f52694a.PartitionedTriangleAbsorption.PhysicalCertificateProducer
/-! # Absorption from aggregate divisibility in a nearly complete F0 host

The query estimate works for every triangle family and every compatible root set.
The absorber theorem specializes to F0: bounded aggregate divisibility is converted
to a bounded physical certificate, and common-neighbour richness is derived from
the missing-degree bound. The constants precede the host and the source.
This is a bounded-source result under explicit density hypotheses, not general [17].
-/
@[expose] public section
namespace PartitionedTriangleAbsorption.NearlyCompleteAbsorber
open Finset BlowupB F0Geometric TypedApplicationLinks PhysicalCertificateProducer SignedCertificate
variable {V : Type*} [Fintype V] [DecidableEq V] {t : ℕ}
end PartitionedTriangleAbsorption.NearlyCompleteAbsorber
