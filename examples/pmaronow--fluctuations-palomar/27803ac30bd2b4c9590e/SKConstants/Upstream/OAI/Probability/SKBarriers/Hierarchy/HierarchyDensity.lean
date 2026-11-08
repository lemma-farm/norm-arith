module

/-
Adapted from OpenAI math, Apache-2.0, commit fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb.
Source: lean/OAI/Probability/SKBarriers/Hierarchy/HierarchyDensity.lean
Changes: public module header and declarations added; import paths moved into SKConstants.Upstream; pinned Lean/Mathlib compatibility changes recorded in the port audit.
Upstream mathematical declarations retained; their namespace OAI is renamed SKConstantsOAI in this distribution.
-/

public import Mathlib
public import SKConstants.Upstream.OAI.Probability.SKBarriers.Hierarchy.HierarchyGaussianLaw
public import SKConstants.Upstream.OAI.Probability.SKBarriers.SpinGlass.SpinStein
public import SKConstants.Upstream.OAI.Probability.SKBarriers.Hierarchy.HierarchyLevels

@[expose] public section

namespace SKConstantsOAI

section
section
noncomputable section
open scoped BigOperators Topology
open MeasureTheory ProbabilityTheory Filter
noncomputable section
open MeasureTheory Set Filter
open scoped Topology Interval
noncomputable section
open MeasureTheory Set
open scoped Interval
noncomputable section
open MeasureTheory Set Filter ProbabilityTheory
open scoped Topology
noncomputable section
open MeasureTheory Set Filter ProbabilityTheory
open scoped Topology NNReal
namespace SK.Analytic
attribute [local instance 2000] parameterNormedGroup parameterNormedSpace

                                                                      
                                                       
                                                  
                                 
                                
                
                                                          
                                                    
                                                                              
                                     

section HierarchyDensity
variable {S : Type} [Fintype S] [Nonempty S] [MeasurableSpace S] [MeasurableSingletonClass S]

                                              
                                                                            
                                                                    

                                                        
                                                                
                                                                                                 
                                                
                                                              
                                                                   
             
                                                              
                                                
             
                                                                       
                       
                                              
                                                                                                     
                                            
          
                                                           

                                                             
                                        
                                                                               
                                                                      
                                                                                         
                                                                                           
                                                                                                     
                                                               
                                                                                      
                                                              
                                                                                 
                                                                                   
                                               
                                                                                   
                                                                         
                                                                 
                         
                                                                          
                                               
                                           
              
                                                                                                    

                                                                    
                                        
                                                                                     
                                                            
                                    
                     
         
           
         
                                                        

                                                        

                                                                           
                                                                               
                         
                                                  
                                                                                                  
                                               
                                                                                                            
                                            
                                                            
                                                      
                                                                     
                                                                                  
                                                              
                                               
                             
        
                 
                              
                     
                                                                                                            
        

end HierarchyDensity
end SK.Analytic

end
end
end
end
end
end
end

end SKConstantsOAI
