-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
import Examples.scottnarmstrong__CaffarelliKohnNirenberg.Dependencies.v49e63fd1c585.CKN.Pressure.CZP1UnconditionalAssembly
import Examples.scottnarmstrong__CaffarelliKohnNirenberg.Dependencies.v49e63fd1c585.CKN.Pressure.IdentificationExtensionGrowthSWS
import Examples.scottnarmstrong__CaffarelliKohnNirenberg.Dependencies.v49e63fd1c585.CKN.Core.Endgame.TheoremBAdaptersCZ
set_option autoImplicit false
set_option warningAsError true
/-!
# Unconditional singly centred pressure bound for theta decay

The suitable-solution slice and residual estimates identify the selected
pressure with the scalar Calderón--Zygmund extension. The component sum
contributes a factor nine, retained in the slice constant. The cylinder
adapter supplies the pressure input shared by the two regularity criteria.
No pressure estimate or source certificate is assumed here.
-/
open MeasureTheory Set
open scoped ENNReal Topology
open CKN.Foundation.Parabolic CKN.Foundation.Euclidean CKN.Core.Step3
set_option autoImplicit false
noncomputable section
namespace CKN
end CKN
