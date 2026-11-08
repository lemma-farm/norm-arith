/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.BPHZ.TreeI3PsiChainBound
public import Phi43.BPHZ.TreeI3PsiPrincipalBound

/-!
# Deterministic diagram bound for the tree `I(Ψ³)Ψ`

For `δK(z, w) = K(z - w) - K(-w)`, the inner product of the chaos components of
`Π̂_0 (I(Ψ³)Ψ)` is, by the closed-form Wick formula
`18 C_ab C_ac² C_cd + 6 C_ac³ C_bd + 18 C_ac² C_ad C_bc` (`a = w`, `b = z`, `c = w̄`, `d = z̄`),
the iterated integral `i3PsiPairing K Q z z'` of
`δK(z, w) δK(z', w̄) [18 Q(w - z) Q(w - w̄)² Q(w̄ - z') + 6 Q(w - w̄)³ Q(z - z')
  + 18 Q(w - w̄)² Q(w - z') Q(w̄ - z)]`.
`i3PsiPairing_bound` shows that it is absolutely integrable and bounded by
`C (s(z - z')^(-δ) + s(z)^(-δ) + s(z')^(-δ) + s(z - z')^(-1) (s(z)^(1-δ) + s(z')^(1-δ)))`,
the union of the pairs `(0, -δ)`, `(-δ, 0)` and `(1 - δ, -1)` of [Hai14, p. 167--168].

Source: [Hai14] = arXiv:1303.5113v4, (10.36)--(10.38), p. 167--168.
-/

@[expose] public noncomputable section

open MeasureTheory

namespace RegularityStructures

                                                                                
                                                                             
                                                
                                                                                   
                                                  

                                                        
                                                                
                                              

end RegularityStructures

end

public section

open MeasureTheory

namespace RegularityStructures

                                                                               
                                        
                                                                                        
                                               
                                                        
      

end RegularityStructures

end
