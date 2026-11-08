-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.GaussianFiberDensity
public import Mathlib.Analysis.InnerProductSpace.ProdL2
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

/-!
# Coordinate independence of canonical whole-field regression

All genuine Gaussian kernels and pointwise pdfs commute with actual coefficient
isometries. This permits local coefficient splits without altering whole-field marks.
-/

@[expose] public section

namespace SlowEquilibration.GaussianRegression

open MeasureTheory ProbabilityTheory Set Function
open scoped RealInnerProductSpace ENNReal Topology

noncomputable section

variable {E D F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup D] [InnerProductSpace ℝ D] [FiniteDimensional ℝ D]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]

                                                                                  
                                                             
                                                
             
                                                          
       
                                                                                             
                                                      

                                                                                               
                                                             
                                                                            
             
                                                                              
                                   

                                                                                    
                                                                 
                                                              
                                             
       
                                                                                               
                                                               
                                                                        

variable [MeasurableSpace E] [BorelSpace E] [MeasurableSpace D] [BorelSpace D]
  [MeasurableSpace F] [BorelSpace F]

                                                                                 
                                                                                    
                                                                                 
                                                                                    
                                                                                                            
                                                                   
                                                                                         
            
                                            
                                                                               
                                                                             
                                                            
                               
                                                                             
                                                                          
                                                                                     

                                                                          
                                       
                                                                              
                                                                 
                                                                               
                                                                        
                       
                                             
                                                                           
                                                                     

                                                                             
                                                        
                                                                                   
                                              
                                                                    
                                             
                                                                                         

end
end SlowEquilibration.GaussianRegression
