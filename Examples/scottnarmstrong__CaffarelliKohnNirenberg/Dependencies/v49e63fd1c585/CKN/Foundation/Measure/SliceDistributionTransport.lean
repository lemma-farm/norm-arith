-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
import Examples.scottnarmstrong__CaffarelliKohnNirenberg.Dependencies.v49e63fd1c585.CKN.Foundation.Measure.SliceMollifierIdentity
set_option autoImplicit false
set_option warningAsError true
/-!
# Change of variables for mollifier pairings

This module records the two reflection identities that move the mollifier
weight off a function and onto the other factor of an integral. In the
elliptic-regularity analysis of Caffarelli--Kohn--Nirenberg (1982), the
convolution `mollify u ε hε x` is the pairing of `u` against the reflected
kernel `y ↦ mollifier ε hε (x - y)`; identifying the two presentations of this
pairing, with `u` replaced by a weak partial derivative, is what lets a weak
derivative be moved from the function onto the test kernel.

Integrating against the volume measure, the change of variables `y ↦ x - y`
(the `ε`-ball reflection) converts the pairing into the convolution itself.
The second identity combines this reflection with the already-proved integral
form of the weak partial derivative, so that a smooth `ψ` may be differentiated
inside the pairing.
-/
open MeasureTheory Metric
open scoped Convolution Topology
set_option autoImplicit false
noncomputable section
namespace CKN
end CKN
end
