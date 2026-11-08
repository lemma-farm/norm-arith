module

/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in LICENSES/Apache-2.0.txt.
Authors: David Sanftenberg
-/
/- Adapted from dbsanfte/RiemannGaussian; provenance and modifications are
recorded in docs/rg-extraction-manifest.json. -/
public import Sidon.NumberTheory.RiemannGaussian.DerivativePowerEnvelope
public import Sidon.NumberTheory.RiemannGaussian.DirichletBlockPowerProfile
public import Sidon.NumberTheory.RiemannGaussian.DirichletDyadicBlocks
public import Sidon.NumberTheory.RiemannGaussian.VinogradovCubicBudget
public import Sidon.NumberTheory.RiemannGaussian.VinogradovCubicSaving
public import Sidon.NumberTheory.RiemannGaussian.VinogradovLongBlocks
public import Sidon.NumberTheory.RiemannGaussian.VinogradovScaleSelection
public import Sidon.NumberTheory.RiemannGaussian.VinogradovSharperBudget
public import Sidon.NumberTheory.RiemannGaussian.VinogradovShortDyadic
public import Sidon.NumberTheory.RiemannGaussian.VinogradovShortResonance
public import Sidon.NumberTheory.RiemannGaussian.ZetaDyadicPowerBound

@[expose] public section

namespace RiemannGaussian.VinogradovCubicDecay
noncomputable section
open RiemannGaussian.VinogradovCubicBudget
open RiemannGaussian.VinogradovSharperBudget (delta line delta_pos delta_le)
                                                           
                                                                        
                                      
                                       
                                                                    
                               
                             
                                                  
                                                                              
                                                                                        
                    
                                              
                                         
           

                                                   
                                                
                                                  
                                                 
                                         
                                                
                                                           
                                      
                                           
                                                        
                         
              
                                                                                          
          

                                                                                 
                                                                               
                                                 
                                                                   
                                                                      
                                                   
                
                                                
             
                                                                                   
                                                                                    
                                                  
                                        
                     
          

def envelope (n : ℕ) (t X : ℝ) : ℝ :=
  Real.exp ((growth n - (Real.log X / Real.log t) ^ 3 / 2097152) * Real.log t)

                                                          
                                   
                                                                       
                                                                           
         
                                                     
            
      

                                                          
                                                       
                                           
                                   
                                                  
            

                                                                       
                                        
                                                           
                                
                              
                           
                                                              
                                                                  
                                           
                             
                                                                             
                                       
                                 

                                                                         
                                                                      
                                
                                          
                                                        
                                            
                                             
                                              
                          

                                                                
                                                
                                                                       
                                           
              
             
                                              
                    

                                                                           
                                                                        
                                         
                                       
                                                   
                                                              
                                                            
                                                                                                 
                                                                      
                                                                       
                                    
                                      
                                                
                                                          
                                                         
                                                                               
                                                                            
                                                     
                                                                             
                        
                                
                      
             
                                                                          
                                                              
                                                           
                                                               
                                            
                                                             
                
                                                              
                                                  
                                                                          
                                           
                                                          
                                                                          
                                                                            
                                                      
                                                                                                
                                                                                                          
                                                                                  
                                                                     
                                      
                                                              
                                                 
                              
                                          
                                                                             
                                                                         
                        
                                   
                                                                              
                                 
                                                                 
                                                          
                                                               
                                              
               
                                         
                                                       
                    
                                                                                  
                 
                                                                    
                                                              
                                                                                 
                                                 
                                                                                               
                                                 
                                                                                
                                     
                                                                                           
                                                           
               
                   
            
                                                            
                                                                
                                                                        
                                    
                                               
                                                       
                             
                                                                
                                                                         
                                   
                                               
                                                       
                             

end
end RiemannGaussian.VinogradovCubicDecay
