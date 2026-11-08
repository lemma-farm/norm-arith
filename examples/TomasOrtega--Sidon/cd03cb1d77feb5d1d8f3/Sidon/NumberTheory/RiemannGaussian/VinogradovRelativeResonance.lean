module

/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in LICENSES/Apache-2.0.txt.
Authors: David Sanftenberg
-/
/- Adapted from dbsanfte/RiemannGaussian; provenance and modifications are
recorded in docs/rg-extraction-manifest.json. -/
public import Sidon.NumberTheory.RiemannGaussian.VinogradovCriticalKorobov
public import Sidon.NumberTheory.RiemannGaussian.VinogradovGaussianBounds
public import Sidon.NumberTheory.RiemannGaussian.VinogradovGaussianCost
public import Sidon.NumberTheory.RiemannGaussian.VinogradovKorobovBilinearPhase
public import Sidon.NumberTheory.RiemannGaussian.VinogradovKorobovMoment
public import Sidon.NumberTheory.RiemannGaussian.VinogradovKorobovPowerSaving
public import Sidon.NumberTheory.RiemannGaussian.VinogradovMeanValue
public import Sidon.NumberTheory.RiemannGaussian.VinogradovRectanglePowerSaving
public import Sidon.NumberTheory.RiemannGaussian.VinogradovRectangleResonance
public import Sidon.NumberTheory.RiemannGaussian.VinogradovResonanceScaling

@[expose] public section

namespace RiemannGaussian.VinogradovRelativeResonance
noncomputable section
open scoped BigOperators
open RiemannGaussian.VinogradovMeanValue RiemannGaussian.VinogradovShiftedMoment RiemannGaussian.VinogradovKorobovMoment
open RiemannGaussian.VinogradovKorobovBilinearPhase RiemannGaussian.VinogradovCriticalKorobov
open RiemannGaussian.VinogradovGaussianBounds RiemannGaussian.VinogradovResonanceScaling
open RiemannGaussian.VinogradovRectangleResonance RiemannGaussian.VinogradovRectanglePowerSaving
open RiemannGaussian.VinogradovKorobovPowerSaving
                                                              
                                                
                            
                                                     
                                                                        
                                                                               
                                                         
                                                  
                        
                                                                                         
                                       
                                                                             
                      
                                                  
                        
                                  
                                                  
                                                                            
                                                      
                                                                 
                                                                 
                                                                    
                                                                         
                                   
                                                                         
                                                                    
                                            
                                     
                         
                                                                
                                               
                  
                                                                                       
                     
                                                                 
                                                                                    
                                                   
                            
                          
                                          
                                                    
                  
                                       
             
        
                                                    
                  
                                       
             
        
                                                                              
                  
                                                      
             
        
                                                                                    
                                           
                                                               
                      
                    
                        
                   
      
                                                         
                                                                
                                                                                                      
            
                                                                             
                                           
                                                                                                              
                                                                             
                                                
                                                    
                                         
                                                                                            
                                                                                       
                                                                       
                                                                                    
                                                     
                         

end
end RiemannGaussian.VinogradovRelativeResonance
