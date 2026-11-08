/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import Examples.jtraverso__typed_triangle_absorption.Dependencies.v61054f52694a.PartitionedTriangleAbsorption.Stage13
public import Examples.jtraverso__typed_triangle_absorption.Dependencies.v61054f52694a.PartitionedTriangleAbsorption.BernoulliExposure
public import Examples.jtraverso__typed_triangle_absorption.Dependencies.v61054f52694a.PartitionedTriangleAbsorption.TruncatedLinkCollisions
/-! # Finite exposure variance and truncated collision sensitivity

This checkpoint formalizes the probability-weighted one-coordinate variance
budget using actual future averages and the two-endpoint sensitivity bound.
The written one-round concentration proof and the iterative nibble are not
claimed as formalized by these imports.
-/
