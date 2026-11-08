-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.

module

public import AVenhance.Infra.Parabolic.FourierGalerkin.ConcreteData
public import AVenhance.Infra.Parabolic.FourierGalerkin.Energy
public import AVenhance.Infra.Parabolic.FourierGalerkin.PathCompactness
public import Mathlib

/-!
# Positive-cutoff Galerkin paths for drift data

This module chooses the finite-dimensional ODE solution at every positive real Fourier cutoff
and records the cutoff-independent scalar energy bound.  The next compactness module consumes
these paths together with the uniform gradient estimate.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set
open Filter
open Homogenization
open scoped Topology

local instance sequenceMeasureSpaceUnitAddCircle : MeasureSpace UnitAddCircle :=
  ⟨AddCircle.haarAddCircle⟩
local instance sequenceMeasureIsAddHaarUnitAddCircle :
    Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance sequenceProbabilityUnitAddCircle : IsProbabilityMeasure
    (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

open scoped RealInnerProductSpace

namespace AVenhance.Infra.Parabolic.FourierGalerkin

local instance scalarTorusMeasureSeparable : IsSeparable (volume : Measure Torus) :=
  inferInstance

local instance two_ne_top_fact : Fact ((2 : ENNReal) ≠ ⊤) := ⟨by norm_num⟩

local instance scalarTorusL2SecondCountable : SecondCountableTopology ScalarTorusL2 :=
  inferInstance

/-- The hypotheses needed to instantiate every positive real Fourier Galerkin system. -/
structure FrozenDriftProblem where
  b : ℝ → Vec 2 → Vec 2
  drift_measurable : AEStronglyMeasurable (fun p : ℝ × Vec 2 => b p.1 p.2)
    (volume.restrict (Icc (0 : ℝ) 1 ×ˢ Set.univ))
  drift_bounded : ∃ B : ℝ, ∀ t ∈ Icc (0 : ℝ) 1, ∀ x, ‖b t x‖ ≤ B
  drift_periodic : ∀ t ∈ Icc (0 : ℝ) 1, IsZ2Periodic (b t)
  κ : ℝ
  κ_pos : 0 < κ
  θ₀ : Vec 2 → ℝ
  initial_memL2 : MemL2On AVenhance.unitCube θ₀

                                                       
                                                                      
                                                                      
                                                                                      
                                    

                                                                                 
                                                                                       
                                                              
                                                                    

                                                                       
                                                                                        
                                                                 
                                                                    
                                                                                   

                                                                                        
                                                                                  
                                      
                                                             
                                                                              

                                                                
                                                                                               
                                                      
                                                

                                                                  
                                                                  
                               
                                                                 

                                                                        
                           
                                  
                                 

                                                                       
                                                                                       
                                                           
                                                                     
                                            
                                                       
                                                     

                                                                                                
                                                                              
                                                                  
                           
                              
                                                          
                                                 
                                                                             
                                                 
                                                                    
                                               
                                                        
                                       
                                    
                                                
                                                                              
                                                                             
        
                                                                      
                                    
                                                   
                                                                                  
                                                
                                                 
                                                            
                            
                                           
                                     
                          
                                  
                                                              
                                          
        
                                                                       
                                                               
                                                        
                                                          
                                 
                                                                      
                                                                  
                                      
              

                                                                                 
                                                                               
                      
                                  
                                                                                      
                              
                                                                          
                                                                                           
                           
                                                                              
                                               
                                                                             
                                                                                   
                                                                  
                                                                          
             
                                                                   
                                                    
                       
                                     
                                  
                                                               
                                                          
                                                     
                                                          
                                                      
                                              
                                                                      
                
                                                   
                                                                           
              
                                                                                            

end AVenhance.Infra.Parabolic.FourierGalerkin

end
