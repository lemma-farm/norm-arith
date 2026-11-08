-- SPDX-License-Identifier: Apache-2.0
-- Adapted from openai/math at fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb (Lean module/public-import adaptation).
module

public import Mathlib
public import SlowEquilibration.Upstream.OAI.Probability.SKGap.Gaussian.GaussianFiniteIBPError
public import SlowEquilibration.Upstream.OAI.Probability.SKGap.Matrix.MatrixCoordinates

@[expose] public section


namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory InformationTheory Real Set
open scoped NNReal ENNReal
open Filter
open scoped Topology
open Matrix Real
open scoped BigOperators Matrix.Norms.Frobenius ENNReal NNReal
namespace SKGap
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

                   
                                                                                               
              

                   
                                                     
                                                                          
                                                                                        
                                                                            
                                               
                                                                                                   
                                                                                     
                                                                                              
                                        
                                                                                          

                                                    
                                                              
                                                           
                                                       
                                       
                                                                    
                                                                                                       
                                                
                                                                        
                                                                                   
                             
                                                                                    
                                                                       
                           
                                             
                            
                                                              
                                              
                                                   
                                             
                                                                                
                                                                     
                                                                                
                                                            
                                                                 
                                  
                                                                                    
                                    
                                                                                           
                                                         
                                                           
                                                    
                                                       
                                         
                                                      
                                                                            
         
                                                           
                                                                   
                                                                      
                                                                           
                    
                                   
      
                                                                          
                                                                          
                                                   
                                                          
                                                     
               
                                                 
                                                       
                          

end SKGap

end

end OAI
