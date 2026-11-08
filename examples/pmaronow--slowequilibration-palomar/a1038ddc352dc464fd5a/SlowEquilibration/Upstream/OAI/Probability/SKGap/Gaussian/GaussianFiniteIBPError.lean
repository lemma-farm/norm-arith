-- SPDX-License-Identifier: Apache-2.0
-- Adapted from openai/math at fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb (Lean module/public-import adaptation).
module

public import Mathlib
public import SlowEquilibration.Upstream.OAI.Probability.SKGap.Localization.CoordinateDeriv

@[expose] public section


namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory InformationTheory Real Set
open scoped NNReal ENNReal
open Filter
open scoped Topology
namespace SKGap
variable {κ : Type*} [Fintype κ] [DecidableEq κ]

                                        
                                                             
                                                  
                                                                    
                                                                                   
                                                                
                                                             
                                                                          
                                                     
                                                       
                                                                                               
                                                              
                                                                                             
                                                                 
                                                        
                                                                   
            
                       
                                                                                               
                                     
                                  
                                     
                                                                              
                                                                                       

end SKGap

end

end OAI
