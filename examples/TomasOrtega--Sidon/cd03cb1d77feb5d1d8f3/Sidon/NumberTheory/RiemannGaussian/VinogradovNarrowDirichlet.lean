module

/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in LICENSES/Apache-2.0.txt.
Authors: David Sanftenberg
-/
/- Adapted from dbsanfte/RiemannGaussian; provenance and modifications are
recorded in docs/rg-extraction-manifest.json. -/
public import Sidon.NumberTheory.RiemannGaussian.DirichletSecondDerivativeBound
public import Sidon.NumberTheory.RiemannGaussian.VinogradovDampedSaving
public import Sidon.NumberTheory.RiemannGaussian.VinogradovDirichletSaving
public import Sidon.NumberTheory.RiemannGaussian.VinogradovKorobovBilinearPhase
public import Sidon.NumberTheory.RiemannGaussian.VinogradovKorobovBlock
public import Sidon.NumberTheory.RiemannGaussian.VinogradovKorobovDamping
public import Sidon.NumberTheory.RiemannGaussian.VinogradovNarrowResonance
public import Sidon.NumberTheory.RiemannGaussian.VinogradovRectanglePowerSaving
public import Sidon.NumberTheory.RiemannGaussian.ZetaPrimeGram
public import Sidon.NumberTheory.RiemannGaussian.ZetaPrimeMomentEnvelope

@[expose] public section

namespace RiemannGaussian.VinogradovNarrowDirichlet
noncomputable section
open scoped BigOperators
open RiemannGaussian.VinogradovNarrowResonance RiemannGaussian.VinogradovRectanglePowerSaving
open RiemannGaussian.VinogradovKorobovBlock RiemannGaussian.VinogradovKorobovDamping RiemannGaussian.VinogradovDampedSaving
                                           
                                                    
                                                                               
                                                         
                                                  
                                                                 
                                                                
                                           
                                          
                                                                     
                                       
                       
                               
                                                                                                 
                      
                        
                  
                        
                                                   
            
            
                                                    
                                                                                                
                                            
                                                                                                               
                              
                              
             
                              
             
                                                        
                                                                     
                                                                                               
                                                                   
                                                                           
                                                                       
                                                  
                                                                                                            
                                                                                                             
                                        
        
                                           
                              
                                                                                    
                                                         
                         
                                          
                                              
                                                    
      
                                                         
                                                               
                                   

                                                 
                                                    
                                                                               
                                                         
                                  
                                   
                                                                                     
                  
                        
                                                 
                                                  
                                       
                                                                                           
                                   
                
                                                           
                                                                 
                                                  
                                                                         
                                 
                  
                                   
                   
         
                                                               
                  
            
     

                                                  
                                                    
                                                                               
                                                         
                                                
                                                               
                                                                   
                                                             
                                                                       
                        
                                                
            
                                                                                         
                    
      

                                                 
                                                                            
                                                                           
                                                                       
                                      
                                                              
                                                             
                                                                       
                                                         
                                                
                                                         
                                          
                                                                        
                       
                                                                                         
                     
                                                              
                                  
                                              
                                  
                                              
                                                  
                                                           
                                                                      
                                                      

end
end RiemannGaussian.VinogradovNarrowDirichlet
