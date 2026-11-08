module

/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in LICENSES/Apache-2.0.txt.
Authors: David Sanftenberg
-/
/- Adapted from dbsanfte/RiemannGaussian; provenance and modifications are
recorded in docs/rg-extraction-manifest.json. -/
public import Sidon.NumberTheory.RiemannGaussian.DirichletBlockPowerProfile
public import Sidon.NumberTheory.RiemannGaussian.DirichletDyadicBlocks
public import Sidon.NumberTheory.RiemannGaussian.VinogradovCubicSaving
public import Sidon.NumberTheory.RiemannGaussian.VinogradovLongBlocks
public import Sidon.NumberTheory.RiemannGaussian.VinogradovScaleSelection
public import Sidon.NumberTheory.RiemannGaussian.VinogradovSharperBudget
public import Sidon.NumberTheory.RiemannGaussian.VinogradovShortDyadic
public import Sidon.NumberTheory.RiemannGaussian.VinogradovShortResonance
public import Sidon.NumberTheory.RiemannGaussian.ZetaDyadicPowerBound

@[expose] public section

namespace RiemannGaussian.VinogradovCubicBudget
noncomputable section
open RiemannGaussian.DirichletDyadicBlocks RiemannGaussian.VinogradovScaleSelection
open RiemannGaussian.VinogradovSharperBudget (delta line delta_pos delta_le line_bounds)
def growth (n : ℕ) : ℝ := 40 * delta n * Real.sqrt (delta n)

                            
                                                            
                                                                     
              
            
      

theorem growth_pos (n : ℕ) : 0 < growth n := by
  unfold growth
  positivity [delta_pos n]

                           
                                                        
                         
              
            
      

                                            
                                                  
                                                
                                                                   
                                                               
            
                                                          
                                                                                                      

                                                          
                                                                       
                                                          
                                                     
                                           
                                                                      
                                                       
                                                  
                                                                   
                                          
                                                                                      
                         
                                                         
                                                                  
                                                                   
                                                                        
                                                                                  
                                    
                                                                            
                                                                                         
                        
                                                                              
                                                                                    
                                    
                                                                                   
                           
             
                                                                                      
                                                                           
                                
                            
                                                            
             

                                                                           
                                               
                                         
                                             
                                                                   
                                                                        
                                                                                  
                                    
                                      
                                                       
                                                
                                                          
                                                                         
                                                              
                                                           
                                                               
                                            
                                                                       
                
                                                                               
                                                               
                                                                              
                         
                                       
                                                                                         
                                                                       
                                                          
                                                                                              
                                                            
                                                               
                                                                                      
                                        
                                                                                     
                                                          
                                                               
                                                                                       
                                       
                                                                                     
                                                          

end
end RiemannGaussian.VinogradovCubicBudget
