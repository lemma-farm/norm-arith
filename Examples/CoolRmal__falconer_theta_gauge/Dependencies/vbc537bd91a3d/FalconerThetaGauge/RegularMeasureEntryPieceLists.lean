/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Examples.CoolRmal__falconer_theta_gauge.Dependencies.vbc537bd91a3d.FalconerThetaGauge.RegularMeasureEntryShellNumbers
public import Mathlib
set_option autoImplicit false
/-!
# The actual lists used for each regular piece

The list adds the entry tube `[0,c]` to the concrete list of `[c,N]`. It has
at most `N²+1` tests, all remaining scheduled anchors lie strictly above `c`,
and restricting the list to such anchors drops precisely the entry tube.
-/
@[expose] public section
noncomputable section
open Finset
open scoped Classical
namespace FalconerThetaGauge
end FalconerThetaGauge
