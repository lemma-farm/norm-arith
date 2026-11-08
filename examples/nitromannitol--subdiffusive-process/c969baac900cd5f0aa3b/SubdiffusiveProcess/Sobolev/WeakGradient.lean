module

public import Mathlib.Analysis.Distribution.TestFunction
public import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff
public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.MeasureTheory.Function.LpSpace.Indicator
public import Mathlib.Analysis.Calculus.FDeriv.Const

@[expose] public section

/-!
# The actual weak-gradient graph

Spatial coordinates use the usual finite product, with its sup norm. Gradient
energy will use the sum of squared coordinate L2 norms, not that sup norm.
The graph below imposes the distributional derivative identity against every
smooth function compactly supported in the open domain. It does not assume
an abstract space has the properties of a Sobolev space.
-/

open MeasureTheory Filter Set TopologicalSpace
open scoped ENNReal ContDiff Distributions
namespace SubdiffusiveProcess
noncomputable section

abbrev SpatialCoordinates (d : ℕ) := Fin d → ℝ
                                                             
                                                           
                                                                
                                   

variable {d : ℕ} {Ω : Opens (SpatialCoordinates d)}

                                                                                   
                                                      
                                                                               

                                                                         
                                                                         
                                                      
                                                                         
                                                                
                                           

                                                                                      
                                    
                                                                                                   
                    

                                                                                  
                                                       
                                                                                                       
                                                
                    

                                                                                          
                                                              
                            
                              
                                                                          
                                                                        

                                                              
                                                                       
                                  
                                                                               

                                                                   
                                                      
                                                         
                                                                
                                                                                                 
                                                                     
                                
                                           
                              
                                                                  
                                                                                               
             
                                                                           
                                   
           
                             
                                               
                         
                             
                                                        
                         
                   

                                                                            
                                   
                                                             
                                                  
                                               
                                                     
                                                         
                                                                  

                                                                          
                                         
                                                                  
                                                    
                                                       
          
              
                                                                  
                                                                                                             
                          
                                                               
                                                                                             
                                                                  
                               
                                       
                         
                                                       
                                                                     
                                  
                                                                                                     
                                             
                           
                                                              

                                                   
                                                                                    
                                                                                       
                                                 
                                                                                  
                                                             

end
end SubdiffusiveProcess
