module

/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in LICENSES/Apache-2.0.txt.
Authors: David Sanftenberg
-/
/- Adapted from dbsanfte/RiemannGaussian; provenance and modifications are
recorded in docs/rg-extraction-manifest.json. -/
public import Sidon.NumberTheory.RiemannGaussian.AnalyticDerivativeCutoff
public import Sidon.NumberTheory.RiemannGaussian.DerivativePowerEnvelope
public import Sidon.NumberTheory.RiemannGaussian.DerivativePowerExponents
public import Sidon.NumberTheory.RiemannGaussian.DerivativeRecursionBudget
public import Sidon.NumberTheory.RiemannGaussian.FiniteLagPowerBounds

@[expose] public section

namespace RiemannGaussian.DerivativePowerStep
noncomputable section
open RiemannGaussian.DerivativePowerExponents RiemannGaussian.AnalyticDerivativeCutoff RiemannGaussian.DerivativeRecursionBudget
open RiemannGaussian.DerivativePowerEnvelope
open scoped Classical

                                                     
                               
                                     
                                                 
                                                        

                                                              
                             
                                                                    
                                           
                                              
                                           
                                                                    
                                                                                
                                           
                                                 
                                             
                                             
                                                        
                                                                        
                                      
                                                              
                                                            
                
        
      
                                                 
                                                                            
                             
                
                                      
                                                                   
               
                                                             
                                                                                 
                                                                                        
                                                                   
                                
               
          
                                               
                                                       
                                           
                                                                       
                                  
                                                                                           
               
                                                           
                                                         
                  
          

                                                                               
                                   
                                                    
                                                                                
                        
                                                    
                                                                                    
                                        
                                                               
                               
                                                                      
                                                
                                            
                                                                      
                                                                       
                                                                    
                                             
                                                
                                                         
                                                             
                                                               
      
                                                                       
                                                      
                                                     
                                                                          
                                                                 
                                                      
                                                                    
               
               
                                           
                
          

                                                                                       
                                         
                                                          
                                                                                      
                              
                                                                              
                                 
                                                
                                              
                                          
                                  
                                                           
                                                                         
                                                                
                                                                   
                                                                                   
                                                   
        
                                                                             
                                                        
                           
                                                                                                
                                                                                               
                                                    
                                                                          
           

                                                                                   
                                         
                                                          
                                                                                      
                                                               
                                 
                                                                       
                                                                    
                                                                       
                                                         
                   
                                                                                     
                       
      
                                                                
                                                                      
               
                                            
                                                                               

end
end RiemannGaussian.DerivativePowerStep
