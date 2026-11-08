/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Analysis.Heat.Decomposition.Vanishing

/-!
# Moments of the heat shells

`∫ z^l D^k (heatShell n)(z) dz = 2^{(3 + |k|_𝔰 - 5 - |l|_𝔰) n} ∫ w^l D^k (heatShell 0)(w) dw`,
and the integral vanishes unless `k ≤ l` componentwise, by integration by parts.  Hence
`|∫ z^l D^k (heatShell n)| ≤ C 2^{-2n}` [Hai14, (5.5)] with `β = 2`.
-/

public section

open MeasureTheory
open scoped ContDiff

namespace RegularityStructures

                                                                              
                                                                      
                                                               
                                                       
                                                               

end RegularityStructures

end
