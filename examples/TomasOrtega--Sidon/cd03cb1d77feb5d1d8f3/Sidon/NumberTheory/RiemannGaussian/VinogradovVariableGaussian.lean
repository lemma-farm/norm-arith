module

/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in LICENSES/Apache-2.0.txt.
Authors: David Sanftenberg
-/
/- Adapted from dbsanfte/RiemannGaussian; provenance and modifications are
recorded in docs/rg-extraction-manifest.json. -/
public import Sidon.NumberTheory.RiemannGaussian.VinogradovGaussianBounds
public import Sidon.NumberTheory.RiemannGaussian.VinogradovGaussianCost
public import Sidon.NumberTheory.RiemannGaussian.VinogradovKorobovMoment
public import Sidon.NumberTheory.RiemannGaussian.VinogradovMeanValue
public import Sidon.NumberTheory.RiemannGaussian.VinogradovRectangleResonance
public import Sidon.NumberTheory.RiemannGaussian.VinogradovResonanceScaling

@[expose] public section

namespace RiemannGaussian.VinogradovVariableGaussian
noncomputable section
open RiemannGaussian.VinogradovGaussianCost (scalar_prefactor_le half_le_tail_denominator)
                                                            
                                         
                                                              
                                                                                    
                             
                                       
                                                                
                                                
                                                                   
                      
                                                                                                      
                                              
                                                               
                                                    
                                                                   
      
                                                
                                                                  
                         
                                                                    
               
                                                                                       
             
           

                                                                   
                                         
                                      
                                                                 
                                                                   
                                 
                                             
                                                                      
        
                                                     
                                                                    
                           
                                                                              
                                                             
                                                        
                                                                  
                                                  
                                               
                                      
                     
      
                                                      
                                                                                           
                                                                     
               
                                           
                         

open RiemannGaussian.VinogradovGaussianBounds RiemannGaussian.VinogradovGaussianKernel RiemannGaussian.VinogradovIntervalResonance
open RiemannGaussian.VinogradovResonanceScaling RiemannGaussian.VinogradovResonanceWindow RiemannGaussian.VinogradovResonancePower
open RiemannGaussian.VinogradovRectangleResonance RiemannGaussian.VinogradovPhaseRectangle
                                                                  
                                       
                                                
                                                                     
                                                         
                                          
                                      
                                                                    
                                                         
                                                                      
                                                                               
                             
                                                                                       
                                                                                       
                     
                  
                                                                                                 

end
end RiemannGaussian.VinogradovVariableGaussian
