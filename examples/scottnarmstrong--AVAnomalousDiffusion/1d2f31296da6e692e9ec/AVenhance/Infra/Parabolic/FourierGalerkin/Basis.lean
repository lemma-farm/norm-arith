-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.

module

public import Mathlib
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-!
# Finite symmetric Fourier cutoffs on the two-torus

The frequency box is indexed by integer pairs and is invariant under negation.  The Fourier partial
sum of a real-valued function is therefore real-valued; the real projection below is its real part,
with a theorem identifying its complexification with the partial sum itself.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open scoped ComplexConjugate ENNReal

local instance basisMeasureSpaceUnitAddCircle : MeasureSpace UnitAddCircle :=
  ⟨AddCircle.haarAddCircle⟩
local instance basisMeasureIsAddHaarUnitAddCircle :
    Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance basisProbabilityUnitAddCircle : IsProbabilityMeasure
    (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

namespace AVenhance.Infra.Parabolic.FourierGalerkin

abbrev Torus := UnitAddTorus (Fin 2)

/-- The integer frequency represented by an ordered pair. -/
def pairFrequency (p : ℤ × ℤ) : Fin 2 → ℤ :=
  fun i => if i = 0 then p.1 else p.2

       
                                                                                   
          
                                      

                                                                
def symmetricFrequencyBox (N : ℕ) : Finset (ℤ × ℤ) :=
  Finset.Icc (-(N : ℤ)) (N : ℤ) ×ˢ Finset.Icc (-(N : ℤ)) (N : ℤ)

                                                         
                                                                           
                                                                               
                                     
                                           
                                    
                                 
                                                    

                                                                   
def complexFourierPartialSum (N : ℕ) (f : Torus → ℝ) (x : Torus) : ℂ :=
  ∑ p ∈ symmetricFrequencyBox N,
    UnitAddTorus.mFourierCoeff (fun y => (f y : ℂ)) (pairFrequency p) *
      UnitAddTorus.mFourier (pairFrequency p) x

/-- The real-valued Fourier projection associated with the symmetric frequency box. -/
def realFourierProjection (N : ℕ) (f : Torus → ℝ) (x : Torus) : ℝ :=
  (complexFourierPartialSum N f x).re

                                                                  
                                                        
                                                    
                                                     
              
      
                                                    
                                                         
                             
                           
                                  
                                               
                                                         
                                  
                        

                                                                
                                                          
                                                                    
                                                              
                                                                     
            
        
                 
                         

                                                                           
                                                                                
                                 
               
                                      
              
                                          
                         
                         
              
                                                         
              
                          
                                                                            
                                                        
                
                                                                                     
                                                          
                                                    
           
                                                                          

                                                                                
                                                                            
                   
                                
                                                                       
                                                            
                                                        
              
                                                

                                                                                       
                                                                        
                                                                                     
          
                                                

end AVenhance.Infra.Parabolic.FourierGalerkin

end
