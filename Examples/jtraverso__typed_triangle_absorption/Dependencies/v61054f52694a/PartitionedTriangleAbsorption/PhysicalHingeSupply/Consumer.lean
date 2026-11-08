/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import Examples.jtraverso__typed_triangle_absorption.Dependencies.v61054f52694a.PartitionedTriangleAbsorption.PhysicalHingeSupply.Supply
public import Examples.jtraverso__typed_triangle_absorption.Dependencies.v61054f52694a.PartitionedTriangleAbsorption.SignedAbsorberAPIStage57
public import Examples.jtraverso__typed_triangle_absorption.Dependencies.v61054f52694a.PartitionedTriangleAbsorption.TypedEmbeddingSelection
/-! # Interface bridges and the native consumer of the physical hinge supplier

**Bridges to existing host interfaces.** The primitive three/four-root queries of the
supplier are exactly `CommonNbrRich 4`. Among the existing interfaces:

* `TypedEmbeddingSelection.Supply p G 4 (ρ n)` is *the same* statement
  (`commonNbrRich_iff_supply`); it is already a hypothesis of
  `ColouredHub.OrderedEmbedding`;
* `CN6 = CommonNbrRich 6` implies it (`commonNbrRich_four_of_cn6`);
* `AntiEdgeful` does **not** imply it (`HingeSupplyFamilyStage58` refutes even the
  weaker conclusion `HingeSupply`), and `Supply p G 2 a` (used by `SharedF0.Host`) only
  controls two roots.

All of these that do imply it are themselves explicit hypotheses; none is derived from the
application host. The application gap is recorded in the Stage 59 report.

**Native consumer.** `signed_absorber_of_commonNbrRich` feeds the supplier into the
already verified signed absorber (`SignedHinge.signed_hinge_absorber`), with
`α = ρ`, `β = ρ^2/4`, `C0 = 6`; anti-edgefulness and non-empty parts are derived from
`CommonNbrRich 4` too, so the only host hypothesis is `CommonNbrRich 4 p G ρ`.
`absorber_of_commonNbrRich_api` is the fixed-host form in the Stage 57 API.
-/
@[expose] public section
namespace PartitionedTriangleAbsorption.PhysicalHingeSupply
open Finset SignedHinge SignedCertificate F0Geometric TypedApplicationLinks
section Bridges
variable {V : Type*} [Fintype V] [DecidableEq V]
end Bridges
section Consumer
end Consumer
end PartitionedTriangleAbsorption.PhysicalHingeSupply
