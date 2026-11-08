/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Analysis.Heat.Decomposition
public import RegularityStructures.Analysis.Heat.Schauder.Reflect

/-!
# `L¹` scaling of the heat shells and their generators

`heatShell n = 2^{-2n} · (heatShell 0)^{2^{-n}}` (rescaled at scale `2^{-n}`), so
`∫ |heatShell n| = 2^{-2n} ∫ |heatShell 0|` and `∫ |L heatShell n| = 2^{2n} ∫ |L heatShell 0|`
(`L = parabolicGenerator`).  These are the `B₀`, `B₁` of the pairing bound
`abs_pairing_reflect_le`.

Source: Hairer, arXiv:1303.5113v4, Lemma 5.5 (scaling of the shells).
-/

public section

open MeasureTheory
open scoped ContDiff

namespace RegularityStructures

                                                                                             
                                                                                     
          
                                                                                   
                                                                                                
                                                   
             
                                                           
                                                                                        
           
                                                       
                           
                                 
      

end RegularityStructures

end
