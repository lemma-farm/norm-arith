-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
import Examples.scottnarmstrong__CaffarelliKohnNirenberg.Dependencies.v49e63fd1c585.CKN.Foundation.Parabolic.Integration.Slice
import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
set_option autoImplicit false
set_option warningAsError true
/-!
# Short-time Hölder estimates

This file records the time-integration estimates used on backward parabolic
intervals.  The right-hand side uses Mathlib's extended-valued `eLpNorm'`,
which agrees with the usual `L^p` norm when the latter is finite and keeps the
statements valid without an extra integrability hypothesis.
-/
open Set MeasureTheory
open scoped ENNReal
set_option autoImplicit false
noncomputable section
namespace CKN
end CKN
