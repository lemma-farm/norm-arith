/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Statistics.Identifiability.IntegrableMarkovExistence
public import Mathlib
/-! # Locally integrable panmictic rates -/

@[expose] public section

open Set Filter MeasureTheory
open scoped BigOperators Topology
namespace Rhone.Statistics.Identifiability

noncomputable def panZeroExtension (f : ℝ → ℝ) : ℝ → ℝ := (Ici 0).indicator f

                                                                             
                                    
                             

                                                                          
                                  
                                        

                                                      
                                                 
                                                       
                            
            
                                                                     
                                                            
                                                                               

                                                                   
                                           
                                          
                              

                                                               
                                       
                                                                   
               
                                                                   

                                                       
                                                                                                 
       
                                                                            

                                                                              
                                                              
         
                                                                
        
                                   

                                                                      
                                                                                 
                                                                                                   
           
                                                                    
                                        
                         
                                   
            
                                        
            
                                   
                         
                          

                                                                            
                                                                  
                                              
                                                                      
                                            
       
                                                                            

end Rhone.Statistics.Identifiability
