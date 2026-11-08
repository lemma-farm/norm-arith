/-
Copyright (c) 2026 Joris van Winden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joris van Winden, OpenAI
-/
module

public import Mathlib.Analysis.Analytic.IsolatedZeros
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Convex.Topology

@[expose] public section

/-!
# Gluing holomorphic time extensions

Holomorphic extensions from disks centered on the real axis agree on overlaps when
their real restrictions agree. The identity principle then glues the local Taylor
extensions into one holomorphic function on a neighborhood of the positive time axis.
-/

open Filter Set Topology

namespace Planarwave

noncomputable section

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]

                                                                                  
                                               
                                                                              
                                                    
                                                    
                                                                               
                  
                                                                  
            
                                                       
                                              
                                                  
                                                      
                                                                                          
                                                                                       
                                            
                                                                         
                                
                                                                         
                                    
                                                                                            
                                                   
                                         
                                                               
                                                                         
                                                                 
                                    
                     
                                                    
                                                                       
                                                                         
                                
                                                                                      

                                                                               
def positiveTimeNeighborhood (η : ℝ) : Set ℂ :=
  ⋃ t : {t : ℝ // 0 < t}, Metric.ball (t.val : ℂ) (η * min t.val 1)

                                                                                  
                                              
                      
                                                                            

                                                                                  
                                               
theorem mem_positiveTimeNeighborhood_of_im_lt {η : ℝ} {z : ℂ}
    (hz : 0 < z.re) (him : |z.im| < η * min z.re 1) :
    z ∈ positiveTimeNeighborhood η := by
  apply mem_iUnion.mpr
  refine ⟨⟨z.re, hz⟩, ?_⟩
  have heq : z - (z.re : ℂ) = (z.im : ℂ) * Complex.I := by
    apply Complex.ext <;> simp
  simpa only [Metric.mem_ball, dist_eq_norm, heq, norm_mul, Complex.norm_I, mul_one,
    Complex.norm_real, Real.norm_eq_abs] using him

                                                                                       
                                                                   
                                                                  
                                    
                                           
        
                                                                                                     
                                                                    
                                                      
                                                      
                                                     
                                                       
                                                             
          

                                                                                 
                                                     
                                                                              
                
                                         
                                                             
                                                   
                                                                 
                                        
           
                                                                           
                                                             
                                                                              
                    
                                                                      
                                 
                                         
                                                                              
                                                                       
                              
                                                    
                                                                        
              
                                                                                          
                                                                                         
                                    
                                                  
                                                                                         
                                    
                                                      
                    
              
                               
                           
                                                             
                         
              
                                                                
                                                               
                           
                                                                              

                                                                                  
                                                                                      
                                                                                
                                                         
                                                         
                                                                                      
            
                                    
                                                                                       
                                     
                                                                                           
            
             
                                                                                            

                                                                   
                                                                  
                                                    
                                         
                                                             
                                                    
                                                           
                                                                 
                                    
                                                       
                                                                              
                                                               
                         
            
                                    
                                                        
                                                                                       
                                     
                             
                                                                                 
              
                            
                                                                                                 
                                                     
                                                                                         
                                    
                                                   
           
                   

                                                                         
                                                                  
                                                                        
                                                  
                                    
                      
                                                                  
                                                                                  
                                           
                             
                                        
                                                                                  

end

end Planarwave
