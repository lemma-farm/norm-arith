/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import Examples.jtraverso__typed_triangle_absorption.Dependencies.v61054f52694a.PartitionedTriangleAbsorption.BernoulliExposure
/-! # The effect of two endpoint changes on truncated link conflicts

The clipped pair-count is the real-valued version of `choose (min degree cap) 2`.
Adding one link edge changes two endpoint degrees; each endpoint contributes
at most `cap`. This supplies the coordinate bound before any concentration
argument, rather than assuming the untruncated collision count is Lipschitz.
-/
@[expose] public section
namespace PartitionedTriangleAbsorption.TruncatedLinkCollisions
end PartitionedTriangleAbsorption.TruncatedLinkCollisions
