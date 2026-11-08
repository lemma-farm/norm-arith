/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
import MarkovProcess.Path.DenseFiltration
import MarkovProcess.Path.Shift
                                                     

/-!
# Restricted restart at rational times

This file turns a full joint-law factorization of the rational past and shifted future into the
event-restricted restart identity on the canonical continuous-path filtration.  The joint-law
factorization remains an explicit input; proving it from the finite-dimensional Markov laws is the
next process-construction step.
-/

open MeasureTheory ProbabilityTheory

namespace MarkovProcess
namespace ContinuousPath

noncomputable section

variable {alpha : Type*} [MetricSpace alpha]
  [MeasurableSpace alpha] [BorelSpace alpha]

/-- Evaluation of a rational past at its terminal coordinate. -/
def densePastTerminal (S : DenseTime) (history : Set.Iic S → alpha) : alpha :=
  history ⟨S, Set.mem_Iic.mpr le_rfl⟩

omit [MetricSpace alpha] [BorelSpace alpha] in
/-- Terminal-coordinate evaluation on rational pasts is measurable. -/
theorem measurable_densePastTerminal (S : DenseTime) :
    Measurable (densePastTerminal (alpha := alpha) S) :=
  measurable_pi_apply (⟨S, Set.mem_Iic.mpr le_rfl⟩ : Set.Iic S)

                                                  
                                                                                               
                              
       
                                                                                               
                                                        
                                                                                  
     

                                                                                               
                                                                                        
                                                               
                                                                
                               
             
                            
                                        
                                                            
                                               
                                                                                  
                                     
                                                        
                                             
                                                                         
                        
                                                                                   
                                                                                
                                    
                                                                         
                                
                                                          
                                                                                    
                                                                          
                                        
                                            
                                                             
                                                                                  
            
                           
                                                                                            
                                                          
            
                
                                                                                   
                                          
                      
                                                                               
                                                                               
                                                                           
           
                
                         

end
end ContinuousPath
end MarkovProcess
