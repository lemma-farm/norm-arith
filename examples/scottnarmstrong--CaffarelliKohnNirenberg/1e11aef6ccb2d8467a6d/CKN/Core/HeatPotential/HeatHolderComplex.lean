-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.

import CKN.Core.HeatPotential.HeatHolderCampanato

open MeasureTheory MeasureTheory.Measure Set Metric Filter
open scoped ENNReal NNReal Topology

set_option autoImplicit false

noncomputable section

namespace CKN.Core.HeatPotential

open CKN.Foundation.Parabolic

                                                                           
                                                                         
                          
                                                          
                               
                                              
                                                        
                                         
                                               
                                                           
                                         
                                               
                                                           
                            
                                                       
                                   
                          
                          
                                              
                                                    
                                              
                                                    
                              
                                                   
                                                                          
                       
                                                                          
                       
                                             
                                                          
                         

                                                                          
                                                                      
              
theorem heat_holder_complex_components_bound
    {gRe gIm : ParabolicPoint → ℝ} {α K p : ℝ}
    (hRe : ParabolicHolderSeminormLE Set.univ gRe α
      (parabolicCampanatoHolderConstant α p * K))
    (hIm : ParabolicHolderSeminormLE Set.univ gIm α
      (parabolicCampanatoHolderConstant α p * K)) :
    ∀ z z' : ParabolicPoint,
      ‖((gRe z : ℂ) + Complex.I * (gIm z : ℂ)) -
          ((gRe z' : ℂ) + Complex.I * (gIm z' : ℂ))‖ ≤
        2 * (parabolicCampanatoHolderConstant α p * K) *
          parabolicDist z z' ^ α := by
  intro z z'
  have hRe' := hRe z (Set.mem_univ z) z' (Set.mem_univ z')
  have hIm' := hIm z (Set.mem_univ z) z' (Set.mem_univ z')
  calc
    ‖((gRe z : ℂ) + Complex.I * (gIm z : ℂ)) -
        ((gRe z' : ℂ) + Complex.I * (gIm z' : ℂ))‖ =
        ‖((gRe z - gRe z' : ℝ) : ℂ) +
          Complex.I * ((gIm z - gIm z' : ℝ) : ℂ)‖ := by
            congr 1
            push_cast
            ring
    _ ≤ ‖((gRe z - gRe z' : ℝ) : ℂ)‖ +
          ‖Complex.I * ((gIm z - gIm z' : ℝ) : ℂ)‖ := norm_add_le _ _
    _ = |gRe z - gRe z'| + |gIm z - gIm z'| := by
      simp only [Complex.norm_real, norm_mul, Complex.norm_I, one_mul,
        Real.norm_eq_abs]
    _ ≤ (parabolicCampanatoHolderConstant α p * K) *
          parabolicDist z z' ^ α +
        (parabolicCampanatoHolderConstant α p * K) *
          parabolicDist z z' ^ α := add_le_add hRe' hIm'
    _ = 2 * (parabolicCampanatoHolderConstant α p * K) *
          parabolicDist z z' ^ α := by ring

end CKN.Core.HeatPotential
