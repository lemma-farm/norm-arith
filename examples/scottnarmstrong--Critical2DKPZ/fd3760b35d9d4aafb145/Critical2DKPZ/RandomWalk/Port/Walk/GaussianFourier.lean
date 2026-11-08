/-
Copyright (c) 2026 Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ahmed Bou-Rabee
Modified for Critical2DKPZ, 2026.
-/
module

public import Mathlib
public import Critical2DKPZ.RandomWalk.Port.Site

/-! # Gaussian Fourier integrals

The complex Gaussian integral along any horizontal line equals the Gaussian density
at the integer frequency times `2π`. -/

@[expose] public section

open MeasureTheory

noncomputable section

namespace LatticeProb.ContinuousTime

/-- The Gaussian kernel of variance `s` at an integer, `(2πs)^{-1/2} e^{-k²/(2s)}`. -/
def lineGauss (s : ℝ) (k : ℤ) : ℝ :=
  (Real.sqrt (2 * Real.pi * s))⁻¹ * Real.exp (-(k : ℝ) ^ 2 / (2 * s))

                                                             
                                                 
                                                              

                                                                              
                                                                       
                                            
                                                                     
                                            
                                           
                                                                   
                                                              
                            
         
         
                   
      

                                                                                  
                                                          
                                 
                                                                      
                               
          

                                                                             
                    
                                                                      
                                                     
                                                                 
                                                                 
                                                
                  
         
                   
      

                                                                             
                      
                                                     
                                                  
                                                   
                                                                        
                               
                                                     
              
         
                                                       
                                                                                
                        

                                                                                      
                                                            
                                                                                          
                                             
                                                   
                                                   
                                                                                          
                                                
                                                                               
                
                                                                 
                                                                                       
                                                                                
                                         
                  
                                           
            
                                                                                       
             
        
                                                           
                                                         
                                   
            
                           
                                                          
                                                                 
                                             

                                                                                         
                                                                                             
                                                                            
                                                   
                                               
                                             
                                                        
                                                             
                                                        
                                                                   
                              

                                                                        
                                                                              
                                                                        
                                             
                                                             
                                                         
                                                   


                                                                                        
def ctGauss (d : ℕ) (t : ℝ) (x : Site d) : ℝ := ∏ i, lineGauss (t / d) (x i)

end LatticeProb.ContinuousTime

end
