-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
import Examples.scottnarmstrong__CaffarelliKohnNirenberg.Dependencies.v49e63fd1c585.CKN.Foundation.Sobolev.Inequalities.Smooth
import Examples.scottnarmstrong__CaffarelliKohnNirenberg.Dependencies.v49e63fd1c585.CKN.Foundation.Sobolev.H1.Basic
import Examples.scottnarmstrong__CaffarelliKohnNirenberg.Dependencies.v49e63fd1c585.CKN.Foundation.Sobolev.Mollify.LpApproximation
import Examples.scottnarmstrong__CaffarelliKohnNirenberg.Dependencies.v49e63fd1c585.CKN.Foundation.Sobolev.Mollify.Transport
import Examples.scottnarmstrong__CaffarelliKohnNirenberg.Dependencies.v49e63fd1c585.CKN.Foundation.Sobolev.WeakDerivative.Product
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
import Mathlib.MeasureTheory.Function.LpSpace.Complete
import Mathlib.MeasureTheory.Function.LpSeminorm.SMul
import Mathlib.MeasureTheory.SpecificCodomains.Pi
import Examples.scottnarmstrong__CaffarelliKohnNirenberg.Dependencies.v49e63fd1c585.CKN.Foundation.Sobolev.Cutoff.NormLeVecEuclidean
set_option autoImplicit false
set_option warningAsError true
/-!
# Local Sobolev and interpolation inequalities for `H¹` representatives
The proof first multiplies the representative by the canonical compactly supported cutoff
inside the outer ball.  The product rule gives a global weak gradient for this zero extension;
global mollification then supplies smooth functions, and Fatou's lemma passes the estimate to the
representative.  This preserves the absolute constant from the smooth estimate.
-/
open MeasureTheory Set Filter
open scoped ENNReal Convolution
namespace CKN
noncomputable section
end
end CKN
