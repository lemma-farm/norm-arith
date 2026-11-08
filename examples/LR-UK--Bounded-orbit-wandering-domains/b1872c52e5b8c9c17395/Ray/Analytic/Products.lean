module
public import Mathlib.Analysis.Analytic.Basic
public import Mathlib.Analysis.Complex.Basic
                               
import Mathlib.Analysis.Analytic.Basic
import Mathlib.Analysis.Analytic.Composition
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
import Mathlib.Basic.Complex.Basic
import Mathlib.Basic.Real.Basic
import Mathlib.Data.Set.Basic
import Mathlib.Data.Stream.Defs
import Mathlib.Data.Stream.Init
import Mathlib.Tactic.Cases
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Topology.UniformSpace.UniformConvergence
import Ray.Analytic.Analytic
import Ray.Analytic.Holomorphic
import Ray.Analytic.Series
import Ray.Misc.Bound
import Ray.Misc.Bounds
                      

/-!
## Infinite products of analytic functions

We define convergence of infinite products, and show that uniform limits of products of
analytic functions are analytic.
-/

open Complex (exp log)
open Filter (atTop)
open Metric (ball closedBall sphere)
open Set
open scoped Classical Real NNReal ENNReal Topology
noncomputable section

variable {ι : Type}

/-!
### Basics about products of sequences
-/

                                   
                                                                          
                                           
                                         
                                                                       

                                                     
                                                                    
                                             
                                                                                               

                                                                                           
                                       
                                                                          
                                                
                     
                                                                                  
                                                                
                                                                     
                         
                                   
                       
              
                               

                                                         
                                                              
                                         
                             

                                                                           
                                                              
                                                
                                                                                        

                                                                   
                                                                                          
                                         
                                              
              
                                                                                         
                             
                                                                                      
                                                
                         
                                   
                                                                   
                                                                 
                            
                                                             
                      

                                            
                                                                           
                                            
                                

                                                              
                                                                     
                                                   
                                                                                                 

                                             
                                                                        
                                                                                      
                                
                                                   

                                              
                                                             
                                                 
                                                                         
                                     

   
                                           
  

                                                                                 
                                                                                   
                                     
                                                                                          
                                                                                  
                                                   
                                                                                   
                                 
                                                       
                
                    
                                
                                             
                              
                                                              
                                               
                                                        
                                           
                                              
                                                    
                                                                   
                 
                                                       
                
                 
                              
                                                       
                                                    
                                  
                           
                                                               
                                          
                            
              
                      
               
                                                                                              
                                                                          
                                                                                       
                                  
                                                                               
                                    
                                                               
                                                                          

                                                                                                  
                                                                                              
                                                                 
                                                            
                                                        
                                                   
                                                             
                                                                                            
                            
                                                             
                                                          
                                
                                                                       
                
                                                                                               
                                                                                      
                                                                  
              
                      
                     
                                                       
                                                               
                                                          
                                                            
              
                         
                    
                             
                                                                     
                                                                            
                                             
             
                             
                                                         
                                               
               
                                                                                              
                                                         
                                                                 
                 
                                               

                                                                  
                                                                                           
                                                                                  
                                                   
                                                                                         
                                                                     
                     
                                   
                                                                      
                                                      

                                                                             
                                                                                                      
                                                                
                                                            
                                                      
                                                           
                                                                            
                     
                                   
                                                                      
                                                      

   
                                       
  

lemma norm_mul_sub_one_le {a b : ℂ} :
    ‖a * b - 1‖ ≤ (1 + ‖a - 1‖) * (1 + ‖b - 1‖) - 1 := by
  -- Ugly semi-GPT 5.1 proof, but meh, it works.
  have h1 : a * b - 1 = (a - 1) * (b - 1) + (a - 1) + (b - 1) := by ring_nf
  have h2 : ‖a * b - 1‖ ≤ ‖(a - 1) * (b - 1) + (a - 1)‖ + ‖b - 1‖ := by
    simpa [h1, add_assoc] using (norm_add_le ((a - 1) * (b - 1) + (a - 1)) (b - 1))
  have h3 : ‖(a - 1) * (b - 1) + (a - 1)‖ ≤ ‖(a - 1) * (b - 1)‖ + ‖a - 1‖ := by bound
  have h4 : ‖a * b - 1‖ ≤ ‖(a - 1) * (b - 1)‖ + ‖a - 1‖ + ‖b - 1‖ :=
    le_trans h2 (by simpa [add_assoc, add_comm, add_left_comm] using add_le_add_right h3 ‖b - 1‖)
  have h5 : ‖a * b - 1‖ ≤ ‖a - 1‖ * ‖b - 1‖ + ‖a - 1‖ + ‖b - 1‖ := by
    simpa [norm_mul, add_comm, add_left_comm, add_assoc] using h4
  grind

                                                              
                                                           
                                                   
                                                        
                                     
                                                 

                                                                                            
                                                                           
                                                               
                                                   
                                                                                                   
                                                                        
                                                                 
                                                  
                                             
                            
                   
                                       
         
                                         
                           
                                                                                         
                                                                                                
                                        
                                                                          
                                         
                                               
                                                        
                                                          
                                                        
               
                 
           
                                                                 
                                                        
                                         
                                                                                               
                                                                
                                                     
                                                                                  
                                                                                     
                               
                                               
