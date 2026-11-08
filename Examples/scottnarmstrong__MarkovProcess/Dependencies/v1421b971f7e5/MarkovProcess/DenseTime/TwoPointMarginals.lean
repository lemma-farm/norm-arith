/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
import Examples.scottnarmstrong__MarkovProcess.Dependencies.v1421b971f7e5.MarkovProcess.DenseTime.TrajectoryMarginals
import Examples.scottnarmstrong__MarkovProcess.Dependencies.v1421b971f7e5.MarkovProcess.Kernel.KolmogorovMoments
import Mathlib.Probability.Kernel.Composition.Lemmas
import Mathlib.Probability.Process.Kolmogorov
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
/-!
# Two-point marginals of the dense-time trajectory, and the intrinsic Kolmogorov bridge

The dense-time trajectory of a conservative sub-Markov kernel semigroup already has identified
one-time marginals.  This file identifies its two-time marginals: at dense times whose physical
images satisfy `iota d < iota d'`, the pair `(path d, path d')` has the law obtained by running
`P` for time `iota d` and then, from the state reached, for the increment `iota d' - iota d`.

The identification is then used to discharge the coordinate Kolmogorov hypothesis that every
trajectory theorem of the library assumes.  Under the intrinsic semigroup bound
`SubMarkovKernelSemigroup.HasKolmogorovMoments`, the canonical dense-time coordinate process is a
Kolmogorov process with a positive Hölder exponent below `(q - 1) / p`.

No continuity, modification, Markov-property, or path-regularity statement is proved here; only
the two-point law and the moment estimate it transports.
-/
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal
namespace MarkovProcess
noncomputable section
namespace DenseTime
end DenseTime
namespace SubMarkovKernelSemigroup
section CompProd
variable {A B C E : Type*} [MeasurableSpace A] [MeasurableSpace B] [MeasurableSpace C]
  [MeasurableSpace E]
end CompProd
section TwoPoint
variable {D alpha : Type*} [MeasurableSpace alpha]
namespace IsConservative
variable [StandardBorelSpace alpha] [Nonempty alpha]
end IsConservative
end TwoPoint
section Bridge
variable {alpha : Type*} [MetricSpace alpha] [MeasurableSpace alpha] [BorelSpace alpha]
  [SecondCountableTopology alpha] [StandardBorelSpace alpha] [Nonempty alpha]
namespace IsConservative
end IsConservative
end Bridge
end SubMarkovKernelSemigroup
end
end MarkovProcess
