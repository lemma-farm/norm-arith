/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
import MarkovProcess.FiniteTime.Kernel
import Mathlib.Probability.Kernel.Composition.KernelLemmas

/-!
# Translation of finite-time kernels

This file proves the finite-dimensional translation identity for a conservative transition-kernel
semigroup. It is ordinary kernel infrastructure and makes no path-space or process-existence claim.
-/

open MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory

namespace MarkovProcess
namespace SubMarkovKernelSemigroup

variable {W X Y Z : Type*}
variable [MeasurableSpace W] [MeasurableSpace X] [MeasurableSpace Y] [MeasurableSpace Z]

                                                                          
                                                                                  
                                                                                   
                                                                             
                      

namespace IsConservative

variable {α : Type*} [MeasurableSpace α]

                                                                                                  
                                                                                           
                                                         
                                                                                        
                  
           
                                                       
                                                                           
                
                                                                          
                                           
                                                      
                                                                     
                                                               
                                                       
                                                                                               
                                                           
                                                                                 

end IsConservative
end SubMarkovKernelSemigroup
end MarkovProcess
