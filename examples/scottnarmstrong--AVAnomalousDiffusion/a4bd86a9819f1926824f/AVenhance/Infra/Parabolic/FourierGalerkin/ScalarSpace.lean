-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.

module

public import AVenhance.Infra.Parabolic.FourierGalerkin.ProjectionCoefficients
public import Mathlib

/-!
# Scalar spatial `L²` synthesis for the real Fourier frame

The orthonormal scalar Fourier modes synthesize an isometric copy of the finite coefficient
space inside scalar torus `L²`. This is the common state space for the cutoff paths and the
coefficient energy estimate.
-/

@[expose] public section

noncomputable section

open MeasureTheory

local instance scalarSpaceMeasureSpaceUnitAddCircle : MeasureSpace UnitAddCircle :=
  ⟨AddCircle.haarAddCircle⟩
local instance scalarSpaceMeasureIsAddHaarUnitAddCircle :
    Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance scalarSpaceProbabilityUnitAddCircle : IsProbabilityMeasure
    (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

namespace AVenhance.Infra.Parabolic.FourierGalerkin

/-- Scalar-valued spatial `L²` on the unit torus. -/
abbrev ScalarTorusL2 := Lp ℝ 2 (volume : Measure Torus)

/-- Every real Fourier mode belongs to scalar spatial `L²`. -/
theorem realFourierModeFin_memLp (N : ℕ) (i : Fin (RealFourierDimension N)) :
    MemLp (realFourierModeFin N i) 2 (volume : Measure Torus) := by
  have hcont := realFourierModeFin_continuous N i
  have hint : Integrable (fun x : Torus => realFourierModeFin N i x ^ 2) volume := by
    exact (hcont.pow 2).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  exact (memLp_two_iff_integrable_sq hcont.aestronglyMeasurable).2 hint

/-- The class of one normalized real cutoff mode in scalar `L²`. -/
noncomputable def realFourierModeL2 (N : ℕ) (i : Fin (RealFourierDimension N)) :
    ScalarTorusL2 :=
  (realFourierModeFin_memLp N i).toLp (realFourierModeFin N i)

/-- Synthesis of a finite real coefficient vector as a scalar torus `L²` function. -/
noncomputable def realFourierScalarMap (N : ℕ) :
    Coefficients (RealFourierDimension N) →L[ℝ] ScalarTorusL2 :=
  ∑ i : Fin (RealFourierDimension N),
    (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin (RealFourierDimension N) => ℝ) i).smulRight
      (realFourierModeL2 N i)

@[simp]
theorem realFourierScalarMap_apply (N : ℕ)
    (c : Coefficients (RealFourierDimension N)) :
    realFourierScalarMap N c =
      ∑ i : Fin (RealFourierDimension N), (c i) • realFourierModeL2 N i := by
  simp [realFourierScalarMap, PiLp.proj_apply]

/-- The scalar cutoff modes remain orthonormal in their `L²` classes. -/
theorem realFourierModeL2_inner (N : ℕ) (i j : Fin (RealFourierDimension N)) :
    inner ℝ (realFourierModeL2 N i) (realFourierModeL2 N j) =
      if i = j then 1 else 0 := by
  rw [MeasureTheory.L2.inner_def]
  calc
    _ = ∫ x : Torus, realFourierModeFin N i x * realFourierModeFin N j x := by
      apply integral_congr_ae
      filter_upwards [(realFourierModeFin_memLp N i).coeFn_toLp,
        (realFourierModeFin_memLp N j).coeFn_toLp] with x hi hj
      simp [realFourierModeL2, hi, hj]
      ring
    _ = _ := realFourierModeFin_orthonormal N i j

theorem ScalarSpace.finiteModeSynthesis_inner {n : ℕ}
    (v : Fin n → ScalarTorusL2)
    (horth : ∀ i j, inner ℝ (v i) (v j) = if i = j then 1 else 0)
    (c d : Coefficients n) :
    inner ℝ (∑ i : Fin n, (c i) • v i) (∑ j : Fin n, (d j) • v j) =
      inner ℝ c d := by
  classical
  rw [sum_inner]
  simp_rw [inner_sum, inner_smul_left, inner_smul_right, horth]
  simp [PiLp.inner_apply, mul_comm]

                                                    
                               
                                                                 
                          
                                          
                                                                  
                                                                     
                                             
                      
                                                                                  

                                                                                          
               
                                                           
                                                                       
                                          

                                                         
                               
                                                                 
                         
                                                       
                                                
                                                   
                                                   
                                               
                                        
                       
                                                            
                                                              
                                    
                    
                                                             
                                                                 
          
                                                         
                                        
                               
                        
                        
        
                                                                              
                                                    
                                                             
                                     
             
                                                           
                                    
             
                                        
                                                          

                                                                     
theorem realFourierScalarMap_norm (N : ℕ)
    (c : Coefficients (RealFourierDimension N)) :
    ‖realFourierScalarMap N c‖ = ‖c‖ := by
  have hinner := ScalarSpace.finiteModeSynthesis_inner (realFourierModeL2 N)
    (realFourierModeL2_inner N) c c
  have hinner' : inner ℝ (realFourierScalarMap N c) (realFourierScalarMap N c) =
      inner ℝ c c := by
    simpa only [realFourierScalarMap_apply] using hinner
  have hleft := real_inner_self_eq_norm_sq (realFourierScalarMap N c)
  have hright := real_inner_self_eq_norm_sq c
  rw [hinner'] at hleft
  nlinarith [hleft, hright, norm_nonneg (realFourierScalarMap N c), norm_nonneg c]

                                                                                                 
                                                                                           
                                          
                                                   
                                                                                     
                                                                            
                                   
                                                      

                                                                                          
                                                                 
                                                               
                                                                                    
                       
               
                                                                                    
                                                                                 
         
                                                          
                                                 
                                   
                           
                                                                             
                  
                                              
             
                                                                       
                                           

end AVenhance.Infra.Parabolic.FourierGalerkin

end
