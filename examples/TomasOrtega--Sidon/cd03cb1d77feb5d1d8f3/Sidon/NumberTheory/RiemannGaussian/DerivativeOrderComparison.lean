module

/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in LICENSES/Apache-2.0.txt.
Authors: David Sanftenberg
-/
/- Adapted from dbsanfte/RiemannGaussian; provenance and modifications are
recorded in docs/rg-extraction-manifest.json. -/
public import Sidon.NumberTheory.RiemannGaussian.DerivativePowerExponents
public import Sidon.NumberTheory.RiemannGaussian.DirichletPowerParameters

@[expose] public section

namespace RiemannGaussian.DerivativeOrderComparison
noncomputable section
open RiemannGaussian.DerivativePowerExponents RiemannGaussian.DirichletPowerParameters
def delta (k : ℕ) : ℝ := ((k : ℝ) + 2) * alpha k

                                                                  
                   
      

theorem delta_pos (k : ℕ) : 0 < delta k :=
  mul_pos (by positivity) (alpha_pos k)

                                                                      
                 
                                                                
                               

                                                             
                                                            
                                        
                                                                                      
              
           
           

                                                                                

                                                                            
                   
               
           
                                
                                                                 
                         

                                                    
                                            

                                                                           

                                                             
                                                        
                        
                                                               
                   
              
                                 
                                                       
                             
              
                                                           
                                                                    
                              
                           
              
               
           
                                                                      

                                                  
                                                                      
                                              
                
                    
                                                         
                                                                             
                                               
                                  
             

                                                    
                     
                                                  
                                                                                      
                                                                               
                                  
                
             
                                            
                                                     

                                                                
              
                 
                                       

end
end RiemannGaussian.DerivativeOrderComparison
