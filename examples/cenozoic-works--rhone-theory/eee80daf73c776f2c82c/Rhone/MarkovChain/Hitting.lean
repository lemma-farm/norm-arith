/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.MarkovChain.AbsorptionProb
public import Rhone.MarkovChain.Trajectory
public import Mathlib
/-! # Absorption as a statement about trajectories -/

@[expose] public section

namespace Rhone.MarkovChain.FinChain

open MeasureTheory ProbabilityTheory Finset Filter Topology

                                                                                           
                                                          
                                              
                    
                               

variable {S : Type*} [Fintype S] [DecidableEq S] [MeasurableSpace S] [DiscreteMeasurableSpace S]
  {C : FinChain S} {A : Finset S}

                       
                                                         
                                                         
           
                 
         
                                                          
                                              
                                                                        
                                                                                            
                                                            
                                    
                     
                                           
                       
                   
                           
                                                             
                                          
                                                          
                                     
                                                      
                                                                             
                                    
                                   
                            
                                                                              
                        
                                                                                                 
                                         
                                                             
                                             
                                                                     
                                                
                                    
               
                
                        

                                                                          
                                                                  
                                                                    
                                                                             
                                                         
         
                                                     
                                                                       
                                                                     
           
                           
                                            
                                                                               
                                                             
                                            
                                                                                           
                                                                                          
                                                            
                                                                       
           
                                 

                                                                            
                                         
                                                                                
           
                                           
                                           
                                                        
                                                 
                                                  
                                                                                        
             
                     
       
      

                                                                                  
                                                               
                                                                          
                                                                
                                                                 
                                                               

                       
                                                                        
                                                        
                                                 
                                       
         
                         
                                          
                                                                                                

                                                                                         
                                                                 
                                             
                                                     
                                                                                         

                                                                                              
                                                                 
                                             
                                                                  
                                                                                        

end Rhone.MarkovChain.FinChain
