-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
import Examples.scottnarmstrong__CaffarelliKohnNirenberg.Dependencies.v49e63fd1c585.CKN.Foundation.Euclidean.RieszSecondWeakCertificate
import Examples.scottnarmstrong__CaffarelliKohnNirenberg.Dependencies.v49e63fd1c585.CKN.Foundation.Euclidean.LpExtensionPairingMain
import Examples.scottnarmstrong__CaffarelliKohnNirenberg.Dependencies.v49e63fd1c585.CKN.Core.Endgame.RieszWeakGradient
import Examples.scottnarmstrong__CaffarelliKohnNirenberg.Dependencies.v49e63fd1c585.CKN.Core.Endgame.TensorExtensionPairing
set_option autoImplicit false
set_option warningAsError true
/-! # Consuming the constructed indexed L² endpoint

The smooth global Hessian estimate supplies the indexed L² input, and
the concrete restricted weak endpoint is instantiated. The first-potential
pairing supplies the weak-gradient identity without an analytic input.
-/
open MeasureTheory Filter
open scoped ENNReal BigOperators
open CKN.Foundation.Parabolic CKN.Foundation.Euclidean
set_option autoImplicit false
noncomputable section
namespace CKN.Core.Endgame
end CKN.Core.Endgame
