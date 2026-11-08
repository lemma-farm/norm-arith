/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
import MarkovProcess.Continuity.DenseTimeContinuousExtension
import Mathlib.Probability.Kernel.Composition.MapComap

/-!
# Transporting dense-time laws to continuous paths

This file transports a kernel on dense-time trajectories to ordinary continuous paths under an
explicit support-on-the-continuous-range hypothesis. It does not prove that support hypothesis.
-/

open MeasureTheory ProbabilityTheory Set

namespace MarkovProcess

noncomputable section

namespace Kernel

variable {β alpha : Type*} [MeasurableSpace β] [TopologicalSpace alpha]
  [MeasurableSpace alpha] [BorelSpace alpha] [T2Space alpha]

variable [StandardBorelSpace (ContinuousPath alpha)]
  [MeasurableSpace.CountablySeparated (DenseTime → alpha)]

                                                                                          
                                                                             
                                                                                        

                                                                                         
def toContinuousPathKernel (κ : Kernel β (DenseTime → alpha))
    (default : ContinuousPath alpha) : Kernel β (ContinuousPath alpha) :=
  Kernel.mapOfMeasurable κ (ContinuousPath.continuousExtension default)
    (ContinuousPath.measurable_continuousExtension default)

/-- The continuous-path transport agrees with the ordinary kernel map. -/
theorem toContinuousPathKernel_eq_map (κ : Kernel β (DenseTime → alpha))
    (default : ContinuousPath alpha) :
    toContinuousPathKernel κ default =
      κ.map (ContinuousPath.continuousExtension default) :=
  Kernel.mapOfMeasurable_eq_map _
    (ContinuousPath.measurable_continuousExtension default)

/-- A Markov dense-time kernel transports to a Markov continuous-path kernel. -/
theorem isMarkovKernel_toContinuousPathKernel (κ : Kernel β (DenseTime → alpha))
    [IsMarkovKernel κ] (default : ContinuousPath alpha) :
    IsMarkovKernel (toContinuousPathKernel κ default) := by
  rw [toContinuousPathKernel_eq_map]
  exact Kernel.IsMarkovKernel.map _
    (ContinuousPath.measurable_continuousExtension default)

                                                                                        
                          
                                                              
                                                                            
                                                
                                                                               
                                                                   
            
                                                                                        
                                                                                      
                                                                 
                                                    
                                   
                                  
                                                              
                                                            
                                       

                                                                                              
                                                         
                                                                            
                                      
                                                                                    
                                                             
              
                           
                                                        
                                                                      
               
                                                                                    
                       
                                  
                                                                                      
                                                                      
                                                               
                                                    

end Kernel
end
end MarkovProcess
