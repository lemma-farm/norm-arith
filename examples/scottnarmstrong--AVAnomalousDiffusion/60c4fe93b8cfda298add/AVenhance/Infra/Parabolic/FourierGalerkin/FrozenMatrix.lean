-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.

module

public import AVenhance.Infra.Parabolic.FourierGalerkin.FrozenDrift
public import AVenhance.Infra.Parabolic.FourierGalerkin.MatrixOperator
public import AVenhance.Infra.Torus.Basic
public import Mathlib
/-!
# Measurable drift Galerkin entries

This module transports the ambient drift hypotheses to the time-dependent entries of a
finite periodic weak-form matrix. The mode and gradient representatives are supplied explicitly;
the real Fourier frame can then use this bridge without changing the weak-form convention.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open Homogenization
open scoped ENNReal

local instance frozenMatrixMeasureSpace : MeasureSpace UnitAddCircle :=
  ⟨AddCircle.haarAddCircle⟩
local instance frozenMatrixMeasureIsAddHaar :
    Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance frozenMatrixProbability : IsProbabilityMeasure
    (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

namespace AVenhance.Infra.Parabolic.FourierGalerkin

variable {n : ℕ}

                                                      
                                                                
                                                         
                                               
                                                        
                                                              
                 
                                                            
                                                        
                                                           
                                                                                        
                                                                                         
                                                                      
             
                         
                                                                       
                                                                                       
                   
                          
                                         
      
                                                                            
                             
                           
         
                                                               
                                                                          
                                                 
                                                                   

                                                                                       
                                                                                               
                                                                                         
                                          
                                                           
                           
                                                                    
                                                        
                                                          
                                      
                                          
                                     
                                                 
                                                                                 
                              
                                                                
                                                           
                                           
                                                               
                                           
                                                                         
                       
                                                                            
                               
                                   
                                                                  
                              
                                                 
           
                                                                          
                                                                     
                                    
                                                                       
                                                                     
                                                               
                                   
                              
                                                                           
                                                                                 
              
                                                                                   
               
              
                             
                                                                      
                                                     
                   
                                                
                                                 
                                                                                         
                                                                  
                                      
                                  
                                   
                                        
                                              
                                                 
                                                                        
                                                  
            
                                                                       
            
                                                        
                                                       
            
        
           
                                              

                                                                                           
                                                           
                                                             
                                                                       
                                              
                                            
                                              
                         
                                                                  
                                 

                                                                                  
                                                                         
                                                      
                           
                                                                    
                                                        
                                                          
                                      
                                          
                                     
                                                 
                                                                                 
                              
                                                                
                                                           
                                           
                                                               
                                           
                                                                         
                       
                                                                            
                                                                                   
                             
                                                                                 
                         
                                                                  
                                       
                                                           
                                                            
                                                                                        
                                                                                           

                                                                                                
                                                                                          
             
                                                    
                                   
                                                                     
                        
                                             
                          
                                                                  
                                     
                                                                                
         
                                             
                               
                                     
                                               
                                           
                                       
                                                                    
                                
                                     
                                                             

                                                                                                                                                                                 
                                                                                     
                                           
                           
                                                                 
                                      
                                          
                                                      
                       
                                                                        
                                                
                        
                                                                                    
                                                                                   
                        
                                                               
                                                              
                              
                                                                
                                                    
                          
                                                                  
                                        
                          
                              
                                        
                                 
                              
                                                              
                                             
                                                                      
                  
                                                       
                              
                                                 
                                         
                
                                            
                                                                                    
                                               
                                                                                     
                         
                          
                                                                               
                    
                                                              
                                                                      
            
        
                                                                                      
                                      
                                                                                          
                                                       
                                                               
                                                       
                                                                    
                                                      
            
                                                                
                                                                   
                                   
                     
                                                                                      
                                                                             
                                             
                                                                          
                                                                                   
                                                                             
                          
                                                                    
                                                  
                                                                                        
                                                                   
                                                                    
                                  
                                                                                
                                     
                                                                
                             
                                                                    
                                                                 
                                      
                                                                
                             
                                                                         
                 
        
      
                        
                                                                
                              
                                                                         
                        
                                        
                                                                                      
                                 
                                
                                                                         

end AVenhance.Infra.Parabolic.FourierGalerkin

end
