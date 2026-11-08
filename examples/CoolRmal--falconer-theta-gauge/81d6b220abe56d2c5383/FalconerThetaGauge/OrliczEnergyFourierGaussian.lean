/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import FalconerThetaGauge.Statement
public import Mathlib
public import Mathlib.MeasureTheory.Measure.CharacteristicFunction.TaylorExpansion
public import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform

/-!
# Planar Gaussian Fourier duality

The Fourier transform here has the manuscript's literal phase `exp(-i ξ · x)`.
The Gaussian duality proof adapts `FalconerPacking/GaussianEnergy.lean`
(Yongxi Lin, Apache 2.0). It uses Mathlib's evaluated Gaussian transform and
Fubini's theorem, with finite measures and explicit positive Gaussian scales.
-/

@[expose] public section

noncomputable section

open MeasureTheory ComplexConjugate
open scoped ENNReal RealInnerProductSpace

namespace FalconerThetaGauge

                                                                       
                                                                              

                                                                          
                                                                                          
                                                                                      

                                                                   
                                                    
                                          

           
                                                                                 
                                                                                 

                                                                            
                                                                                      
                                                                      
                                                              
                                                                      
                                                             
          
         
      

                                                                                          
                          
                                       
                                                                                
                           
                                                                                      
                                                                   
                                                  
                                          
                                                   

                                                                               
                          
                                                                 
                                                                              
                                               
                                                                               
                                                

                                                                                           
                                                                                  
                                                              
                                   
                                                
                                                                                      
                          
           
                                                                                       
        
                  
                                                                          
                                                        
                                         
                                                               

                                                                                    
                                                                      
                                                                                       
                          
                                                                           
                                        
                                                               
                                                                                   
                                              
                                                    
                         
                                                                            
                           
             
       
                     
                                                                              
                                 
                                                                      

end FalconerThetaGauge
