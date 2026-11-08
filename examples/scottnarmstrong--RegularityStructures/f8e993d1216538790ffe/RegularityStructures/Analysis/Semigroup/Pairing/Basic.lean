/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Analysis.Semigroup.Operator

/-!
# Pairing of a `Q`-distribution with a test function: definitions

A `Q`-distribution `Λ` (a family `Λ_t = Q_t Λ`, see
`RegularityStructures.Analysis.Semigroup.Basic`) is paired with a
function `φ` by `⟨Λ, φ⟩ = lim_{s ↓ 0} ∫ Λ_s φ dμ`.

* `pairing`: this limit (`limUnder`; when the limit does not exist the value is an unspecified
  junk value chosen by `Classical.epsilon`, so every use must come with a convergence statement);
* `IsGeneratorPair φ ψ`: `ψ = Lφ` in integrated form, `Q_h φ - φ = ∫_0^h Q_v ψ dv`;
* `IsSymmetric`, `IsMetricScale`: symmetry of the kernel, and `scaleDist` being a metric-like size;
* `IsLocalOrder Λ x₀ γ A C`: `Λ` is "of order `γ` at `x₀`", the hypothesis on
  `Rf - Π_{x₀} f(x₀)` in the reconstruction bound [Hai14, Theorem 3.10, (3.3)];
* `pairingConst A`, the constant in the bound `|⟨Λ, φ^λ_{x₀}⟩| ≲ λ^γ`.

Source: [Hai14] = arXiv:1303.5113v4.
-/

@[expose] public noncomputable section

open MeasureTheory Filter
open scoped Topology

namespace RegularityStructures.RegularisingSemigroup

variable {E : Type*} [MeasurableSpace E] {μ : Measure E} (K : RegularisingSemigroup E μ)

                                                                                       
                                                                               
                                                      

                                                                        
                                
                                           
                                                                                

                               
                                                                  

                                                                      
structure IsMetricScale : Prop where
  symm : ∀ x y, K.scaleDist x y = K.scaleDist y x
  triangle : ∀ x y z, K.scaleDist x z ≤ K.scaleDist x y + K.scaleDist y z

                                                                                              
                                                                                           
                                               
                               
                                                          

                                           
                                                                             

                                                                                             
                                                            
                                                   
                                                                          

end RegularityStructures.RegularisingSemigroup

end

public section

open MeasureTheory Filter
open scoped Topology

namespace RegularityStructures.RegularisingSemigroup

variable {E : Type*} [MeasurableSpace E] {μ : Measure E} (K : RegularisingSemigroup E μ)

            
                                                                 
                                                                                      
               

end RegularityStructures.RegularisingSemigroup

end
