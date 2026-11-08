/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Moments.KernelLimit
public import Critical2DKPZ.Definitions.RescaledP2P
public import Critical2DKPZ.Polymer.Moments
import Critical2DKPZ.Analysis.Lattice.Basic
import Mathlib.Tactic

/-! # First moments under diffusive rescaling

Even ceilings determine the time intervals and nearest-even cells determine the spatial sampling; the annealed kernel converges to the planar heat kernel. -/

public section

noncomputable section

open MeasureTheory Filter
open scoped Topology

namespace Critical2DKPZ.SHF.Moments

                                                                         
                                                        
                                                                                                 
                                                                    
         
                                                        
                          
                                                

                                                                 
                                                                          
                                  
                 
       

                                                                                               
                                                                      
                                                   
                                                              
                                                                                              
                                                                                              
                                                 
                                     
                          
      

                                                                                       
theorem integral_rescaledP2P (ϑ : ℝ) (N : ℕ) (s t : ℝ) (p : Plane × Plane) :
    (∫ ω, rescaledP2P ϑ N s t p ω ∂disorderLaw) =
      (N : ℝ) / 4 * srwKernel (evenCeil ((N : ℝ) * t) - evenCeil ((N : ℝ) * s))
        (latticePoint N p.2 - latticePoint N p.1) := by
  change (∫ ω, (N : ℝ) / 4 * pointToPoint _ _ _ _ _ ω ∂disorderLaw) = _
  rw [integral_const_mul, Polymer.integral_pointToPoint]

                                                                                                      
                                                                                 
                         
                                                                    
                                                      
                                
                                                                                       
                                       
                                                               
                                                                         
                                     

end Critical2DKPZ.SHF.Moments
