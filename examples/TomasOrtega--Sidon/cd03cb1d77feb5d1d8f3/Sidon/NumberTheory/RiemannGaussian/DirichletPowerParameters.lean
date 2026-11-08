module

/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in LICENSES/Apache-2.0.txt.
Authors: David Sanftenberg
-/
/- Adapted from dbsanfte/RiemannGaussian; provenance and modifications are
recorded in docs/rg-extraction-manifest.json. -/
public import Sidon.NumberTheory.RiemannGaussian.DerivativePowerExponents

@[expose] public section

namespace RiemannGaussian.DirichletPowerParameters
noncomputable section
open RiemannGaussian.DerivativePowerExponents
def line (k : ℕ) : ℝ := 1 - ((k : ℝ) + 2) * alpha k

                                                            

                                                   

                                                                                
                  
                    
                
                                                        
             
                                          

                                                                          
                                 
              
                  
                                      
                              

                                              
             
                                     

                                              
             
                                                                                
          

                                                              
                                                                    
           
                    
                      
                  
                                                          
               
                                            
                                       
                                                      
                
                    
                                         
                  
                                        
            
             
           
          

                                                                                  
                                            
                                 
                                                        
                                                    
                  
              
          
            
         
            
      

                                                                          
              
                                  

                                             
               
                      
                        
            

                                                                               
                           
                                                                                
            

end
end RiemannGaussian.DirichletPowerParameters
