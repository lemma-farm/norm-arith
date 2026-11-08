/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.Definitions.HeatKernel
public import Critical2DKPZ.Analysis.Heat.Basic
public import Critical2DKPZ.SHF.DeltaBose.CollisionWords
public import Critical2DKPZ.SHF.DeltaBose.ScalarDensity
import Mathlib

/-! The free and fused kernels in Tsai’s equations (2.1)–(2.5) use product Lebesgue measure, a collision coefficient of `4π` and center heat time `t/2`. -/

@[expose] public section

open MeasureTheory

namespace Critical2DKPZ.DeltaBose

                                                                               
                                             

                                                   
abbrev Spectator {n : ℕ} (α : CollisionPair n) :=
  {i : Fin n // i ≠ α.1.1 ∧ i ≠ α.1.2}

                                                                            
                                                                                        

                                                                                       
                                                                                 
                               
                                                                 

                                                                               
                                                                     
                                           
                          
         
                           
           
                        
                                                     


                                                            
                                                                                     
                                  

                                                    
                                                                                
                                             
                                    

                                                   
                                 
                                                                              
                   
                        
                           
              
                
                                                                
                                               
                          
              
              
                
                                          

                                    
                                                                           
                               

                                                              
                                                                      
                                                           
                                           

                                                              
                                                                        
                                                                
                                                                  

                                                                                                                                                   
                                                                         
                                       
                                                                    
                                                   

                                                      
                                                                             
                             
                                                              

                                                                                     
                                                                             
                                                                                    
                         


                                         
                                                                                      
                                                                      
                        
                                                                     
                                                                             
                                                                  

                                                     
                                                                 
                                                 
                             
           
                                            

                                                                    
                                                                   
                                                           
                                                          
                         

                                                                
                                                                    
                                                                                              
                        
                                        
         
                             
           
                                                



                                                                         
                                                        
                                                                        

end Critical2DKPZ.DeltaBose
