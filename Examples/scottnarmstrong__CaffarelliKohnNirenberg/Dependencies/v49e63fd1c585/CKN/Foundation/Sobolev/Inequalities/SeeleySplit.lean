-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
import Examples.scottnarmstrong__CaffarelliKohnNirenberg.Dependencies.v49e63fd1c585.CKN.Foundation.Sobolev.Inequalities.SeeleyBounds
set_option autoImplicit false
set_option warningAsError true
/-!
# Splitting the two-reflection energy integral

This module isolates the `ENNReal` integral algebra from concrete energy
densities.  The resulting theorem is applied only after the density has been
made opaque at the use site.
-/
open Set MeasureTheory
open scoped ENNReal
namespace CKN
end CKN
