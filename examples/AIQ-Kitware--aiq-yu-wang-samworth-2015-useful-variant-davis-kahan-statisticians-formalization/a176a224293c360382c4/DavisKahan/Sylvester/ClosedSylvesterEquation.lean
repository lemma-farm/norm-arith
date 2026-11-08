/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Thinking
-/
import ForTauCeti.Analysis.OperatorIdeal.Family.OperatorNorm
import DavisKahan.SpectralTheory.PartialMap.Basic
import ForTauCeti.Analysis.InnerProductSpace.LinearPMap.Sylvester
import Mathlib

/-!
# Closed Sylvester equations and everywhere-bounded inverses

The proved front of the unbounded spectral development: the closed Sylvester
equation interface, closed resolvent data, and everywhere-defined bounded
inverses.  The spectral projection and truncation theory that is still open
stays in `DavisKahan.InfiniteDimensional.Core.UnboundedSpectral`.
-/

namespace TauCeti
namespace DavisKahan
namespace ExactSinTheta

open scoped InnerProductSpace
open scoped Topology
open Filter

universe u v

variable {𝕜 : Type u} [RCLike 𝕜]
variable {E F : Type v}
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]


namespace SylvesterEquation

                                           
                                                                           
                                                                        
                       
                                     
                     
                                                      
                                                
                                                 
                          
             
                                    
                                            
                     
       
           
           

end SylvesterEquation

end ExactSinTheta
end DavisKahan
end TauCeti