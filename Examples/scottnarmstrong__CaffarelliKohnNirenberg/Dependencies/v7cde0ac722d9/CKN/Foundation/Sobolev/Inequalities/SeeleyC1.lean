-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
import Examples.scottnarmstrong__CaffarelliKohnNirenberg.Dependencies.v7cde0ac722d9.CKN.Foundation.Sobolev.Inequalities.Seeley
set_option autoImplicit false
set_option warningAsError true
/-!
# The `C¹` Seeley extension

This file supplies the global differentiability and compact-support interface for the
two-reflection extension.  The derivative is glued across the unit sphere using the
matching identities from `Seeley`.
-/
open Set
open scoped Topology
namespace CKN
noncomputable section
attribute [local instance] Classical.propDecidable
end
end CKN
