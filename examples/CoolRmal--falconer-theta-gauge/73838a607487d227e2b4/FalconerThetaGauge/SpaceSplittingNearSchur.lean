module

public import FalconerThetaGauge.SpaceSplittingNearCells
public import FalconerThetaGauge.MaskedFourierCells
public import FalconerThetaGauge.MaskedFourierArcEnergy
public import Mathlib
/-! # Literal occupied-cell expansion and the `81²` near-row Schur bound -/

@[expose] public section

noncomputable section

open MeasureTheory Set Function Finset
open scoped Classical RealInnerProductSpace

namespace FalconerThetaGauge

open GaugeFrostman GaugeSeparatedMeasures

def spaceSplittingJointAmplitude (ρ₁ ρ₂ : Measure Plane) (X Y : Set Plane)
    (b₁ b₂ : Plane → UnitCircle → ℝ) (z : ℝ × UnitCircle × UnitCircle) : ℂ :=
  maskedFourierAmplitude ρ₁ X b₁ z.1 z.2.1 * maskedFourierAmplitude ρ₂ Y b₂ z.1 z.2.2

@[fun_prop]
theorem measurable_spaceSplittingJointAmplitude (ρ₁ ρ₂ : Measure Plane)
    [SFinite ρ₁] [SFinite ρ₂] (X Y : Set Plane)
    {b₁ b₂ : Plane → UnitCircle → ℝ} (hb₁ : Measurable (uncurry b₁))
    (hb₂ : Measurable (uncurry b₂)) :
    Measurable (spaceSplittingJointAmplitude ρ₁ ρ₂ X Y b₁ b₂) :=
  ((measurable_maskedFourierAmplitude ρ₁ X hb₁).comp
    (measurable_fst.prodMk (measurable_fst.comp measurable_snd))).mul
    ((measurable_maskedFourierAmplitude ρ₂ Y hb₂).comp
      (measurable_fst.prodMk (measurable_snd.comp measurable_snd)))

theorem norm_spaceSplittingJointAmplitude_le (ρ₁ ρ₂ : Measure Plane)
    [IsFiniteMeasure ρ₁] [IsFiniteMeasure ρ₂] (X Y : Set Plane)
    {b₁ b₂ : Plane → UnitCircle → ℝ} (hb₁ : Measurable (uncurry b₁))
    (hb₂ : Measurable (uncurry b₂)) (hbound₁ : ∀ x w, |b₁ x w| ≤ 1)
    (hbound₂ : ∀ x w, |b₂ x w| ≤ 1) (z : ℝ × UnitCircle × UnitCircle) :
    ‖spaceSplittingJointAmplitude ρ₁ ρ₂ X Y b₁ b₂ z‖ ≤
      ρ₁.real X * ρ₂.real Y := by
  rw [spaceSplittingJointAmplitude, norm_mul]
  exact mul_le_mul (norm_maskedFourierAmplitude_le_mass ρ₁ X hb₁ hbound₁ _ _)
    (norm_maskedFourierAmplitude_le_mass ρ₂ Y hb₂ hbound₂ _ _) (norm_nonneg _)
    measureReal_nonneg

theorem memLp_spaceSplittingJointAmplitude (ρ₁ ρ₂ : Measure Plane)
    [IsFiniteMeasure ρ₁] [IsFiniteMeasure ρ₂] (X Y : Set Plane)
    {b₁ b₂ : Plane → UnitCircle → ℝ} (hb₁ : Measurable (uncurry b₁))
    (hb₂ : Measurable (uncurry b₂)) (hbound₁ : ∀ x w, |b₁ x w| ≤ 1)
    (hbound₂ : ∀ x w, |b₂ x w| ≤ 1) (K v : ℕ) :
    MemLp (spaceSplittingJointAmplitude ρ₁ ρ₂ X Y b₁ b₂) 2
      (maskedFourierJointMeasure K v) :=
  MemLp.of_bound
    (measurable_spaceSplittingJointAmplitude ρ₁ ρ₂ X Y hb₁ hb₂).aestronglyMeasurable
    (ρ₁.real X * ρ₂.real Y) (Filter.Eventually.of_forall
      (norm_spaceSplittingJointAmplitude_le ρ₁ ρ₂ X Y hb₁ hb₂ hbound₁ hbound₂))

                                                                                    
                                                       
                                                                               
                                                      
                                                                   
                                                                   
                                       
                                                                                  
                                                      
                                           
                                                               
                                            
                                          
                                                                              
                                                                            
                                  
                              
                

                                                                                       
                                                                          
                                                       
                                                                               
                                                      
                                                                   
                                                                               
                                                       
                                        
                                                           
                                                                               
                              
                                                                   
                                                                                      
                                                               
                     
                                                                
                                       
                                                                
                                       
                                                 
            
                                                     
                                      
                                              
                                                                                  
                         
                                                                         
             
                                                       
                                 
                                                                                        
                 
                                            
                                                                                
                                                                                
                                                                                        
                                  
            
                                                                                    
                               
                                                                           
                                                                           
         
                                                                                  
                                                                                     
                    
                                   
                     
           
                                                                                

end FalconerThetaGauge
