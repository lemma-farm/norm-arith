-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.G2.MaxGauge
public import RothschildStein.Definitions.HomogeneousGroup.mul
public import RothschildStein.Definitions.HomogeneousGroup.inv
public import Mathlib
set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
open Set
open scoped BigOperators
namespace RothschildStein.G2

/-- Homogeneous norm, with one constant for inversion and multiplication
(BB Definition 3.8, pp. 98–99). The analytic gauge axioms use the predicate. -/
structure HomogeneousNorm {N : ℕ} (G : HomogeneousGroup N) where
  toFun : (Fin N → ℝ) → ℝ
  gauge : G.IsHomogeneousGauge toFun
  c : ℝ
  one_le_c : 1 ≤ c
  inv_le : ∀ x, toFun (G.inv x) ≤ c * toFun x
  mul_le : ∀ x y, toFun (G.mul x y) ≤ c * (toFun x + toFun y)

instance HomogeneousNorm.instCoeFun {N : ℕ} {G : HomogeneousGroup N} :
    CoeFun (HomogeneousNorm G) (fun _ => (Fin N → ℝ) → ℝ) := ⟨HomogeneousNorm.toFun⟩

variable {N : ℕ} {G : HomogeneousGroup N}

                                                                               
                                                                                      

                                                                              
                                                            
                              

                                                         
                                                        
       
                                                                        

                                                                     
       
                                                    

                                                                  
                         
                                                                           
                                  
                                    
                                                                                  
                                                          

                                                                  
                                                                            
                                  
                                                 
                                            
                                                      

                                                                        
                                                                     
                                             
                                                             

                                                                 
                                                     
                                                                         
                                                         
                                                       
            
                   

                                                                    
                                                       
                                                                                  
                                   
                                                 
                                                     
                                        
                                     
                                                               
                                                         
                         
             
                                             
                      
                                                     
                                                                                           
                                                                                           
                              
           
                                   
                                      
                       
                     
                              
           
                                   
                                      
                       
                     
                                                                       
         
                     
           
                                                   
        
                              
                                       
                          
                          
                                                       
                                               
                        
               
          
                                                   
                                                                               
                           
          
                                                 
                                                               
                                        

                                                                               
                                                                              
                                                       
                                                         
                                                               
                                       
            
                            
               
                             

                                                                            
                                                 
                                                                 
                                                                       
                                                           
                                                           
                                                                 
         
             
        
                                                                         
                                                                
                                                               
                          
                       
                                                              
                                                               
        
                                                             
                                                                
                                  

end RothschildStein.G2
