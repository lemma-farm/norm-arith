-- Copyright (c) 2026 Scott Armstrong and Tuomo Kuusi.
-- Released under Apache 2.0 license.
-- From CoarseGraining (https://github.com/scottnarmstrong/CoarseGraining), commit c7ddd76.

module

public import Homogenization.Ambient.Basic
public import Mathlib
public import Mathlib.Analysis.Calculus.ContDiff.Basic
public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Analysis.Calculus.FDeriv.Add
public import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
public import Mathlib.MeasureTheory.Function.LocallyIntegrable
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

@[expose] public section

namespace Homogenization

def basisVec {d : ℕ} (i : Fin d) : Vec d :=
  Pi.single i (1 : ℝ)

                                                      
                                               
                    
           
                   
                      

                                                                                           
                                                              
                                     
                        
                             
        
                   
              
            
              

                                                                                           
                                                               
                                     
                        
                             
        
                   
              
            
              

                                                                 
                                                
                                    
                                      
                 

def HasWeakPartialDerivOn {d : ℕ} (U : Set (Vec d)) (i : Fin d)
    (u gi : Vec d → ℝ) : Prop :=
  ∀ φ : Vec d → ℝ,
    ContDiff ℝ (⊤ : ℕ∞) φ →
    HasCompactSupport φ →
    tsupport φ ⊆ U →
    ∫ x in U, u x * (fderiv ℝ φ x) (basisVec i) ∂MeasureTheory.volume =
      -∫ x in U, gi x * φ x ∂MeasureTheory.volume

def HasWeakGradientOn {d : ℕ} (U : Set (Vec d)) (u : Vec d → ℝ) (Du : Vec d → Vec d) : Prop :=
  ∀ i : Fin d, HasWeakPartialDerivOn U i u (fun x => Du x i)

namespace HasWeakPartialDerivOn

                                                             
                                                       
                                     
                                                                          
                                                                          
                                          
                                            
                                                   
                   
                                                               
                                                          
                                                        
                                       
                                                       
                
                                                                          
                                                                    
                
                                                                          
                                                                    
                 
                                                                     
                                    
                               
                                                                         
                 
                                                                     
                                    
                               
                                                                         
                    
                                                  
                
                                                  
                    
                                                  
                
                                                  
                  
                                                      
                                                 
                                              
                                                                 
                  
                                                      
                                                 
                                              
                                                                 
                  
                                                    
                                                          
                                                    
                                                    
                         
                         
                    
                                                                     
          
                                                           
                                                                             
                                                                          
                          
                    
                                                        
                                                              
                                                               
                                          
                    
                                                  
                
                                                                  
                                                      
        
                                                    
                                                                
                                
                                                                   
                                                                                        
                        
                                                                           
                                           
                               

end HasWeakPartialDerivOn

end Homogenization
