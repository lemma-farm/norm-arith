-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.

module

public import AVenhance.Infra.Torus.Calculus
public import AVenhance.Infra.Torus.Fourier
public import Mathlib

/-! Fourier coefficients of smooth periodic functions and their derivatives. -/

@[expose] public section

noncomputable section

open MeasureTheory Set
open Homogenization
open scoped ComplexConjugate

local instance avInfraTorusFourierCalculusMeasureSpace1 : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance avInfraTorusFourierCalculusMeasureIsAddHaarMeasure2 : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance avInfraTorusFourierCalculusIsProbabilityMeasure3 : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

namespace AVenhance.Infra.Torus

                                                                           
                                                
                                                             
                                              

                                                                                   
                                                                     
                                             

def FourierCalculus.closedCell (d : ℕ) : Set (Vec d) :=
  Set.pi Set.univ fun _ => Set.Icc (0 : ℝ) 1

theorem FourierCalculus.isCompact_closedCell (d : ℕ) : IsCompact (FourierCalculus.closedCell d) := by
  simpa [FourierCalculus.closedCell] using (isCompact_univ_pi fun _ : Fin d => isCompact_Icc)

                                                                      
                                                                                                 
                                                                                
         
                                                                   
                                                                                
                             

                                                                                          
theorem measurable_unitTorusRepresentative (d : ℕ) :
    Measurable (unitTorusRepresentative d : UnitAddTorus (Fin d) → Vec d) := by
  have heq : unitTorusRepresentative d = fun x =>
      ((UnitAddTorus.measurableEquivPiIoc (fun _ : Fin d => (0 : ℝ)) x).val) := by
    funext x i
    rfl
  rw [heq]
  exact measurable_subtype_coe.comp
    (UnitAddTorus.measurableEquivPiIoc (fun _ : Fin d => (0 : ℝ))).measurable

                                                                                
                                     
                                                           

                                                                                 
                                                                                    
                                                                           
                                                                               
                                                                                                   
                                                                       
                                                      
                                                       
                                                  
                                                        
                              
                       
                                                                                                  
                                                                                                      
       
                     
                                              
                                                     
                      

                                                                    
                                                                                 
                
                                                     

theorem continuous_coordDeriv {d : ℕ} (i : Fin d) {f : Vec d → ℂ}
    (hf : ContDiff ℝ 1 f) : Continuous (coordDeriv i f) := by
  exact (hf.continuous_fderiv (by simp)).clm_apply continuous_const

                                                         
                                         
                                                     
                                                                                   
            
                                                                           
                                     
                               
              
           
             
                                          
           
               
                     
            
                                                            
                                                          
                                         
                                                     
                                                          
                       
       
         

                                                         
                                         
                                                                   
                                 

                                                                 
                                                         
                                                                                    
                                      
      
                                                       
                                   
                                                                  
                             
                                                
                                                                       
                                                         
                                                
                                                    
                             
                           
                                                                             
                                  
                                                         
                                           
                                              

                                                                    
                                         
                                                                
                                        
                                       
      
                                                                
                                            
                             
                                                
                                  
                                          
                                   
                                                                           

                                                                   
                                                            
                         
                                                              
                                          
                                 
                                                      
             
                                                               
                                                   
                                                                                  
                                           
                                                                      
                
                                               
                                          
                                                                           
                                 
                           
         
                                         
                                                                   

                                                                        
                                               
                                        
                                            
                                                                               
                                                                    
                                       

                                                                                
                                               
                                                            
                                               
                                                   
                           
                                                        
                                                        
                                                    
           
                                                                  
                                                                 
                   
                      
                
        
        

                                                                           
                                             
                                       
                                                                       
                        
                                         
                                          
            
                                                         
                                                              
                                                     
                                                                       
      
                                       
                                                                       
               
                                                               
                                                
                                                          
                                                                                 

                                                                   
                                                               
                                                                      
                           
                                           
                                                                          
                                                 
                                               
                                            
                                                        
                                                                       
           
                                                         
                                                                  
                                                   
                 
                                                                          
                                        
        
                                                                        
                                                                       
                                                                   
                                 
                     
            
                                          
                                                   
                       
                                                                                      
      
                                                                                 
                                                                            
              

                                                                   
                                            
                                              
                                        
                                                         
           
                                            
                 
                        
                                
                                                  
                
                                              
                          
                                                       

                                                                             
                                                 
                                                    
                                                 
          
                                 
                                                                       
                                                                                
                                                     
                                                            
                                                              
            
                                                                 

theorem FourierCalculus.continuous_integrableOn_closedCell {d : ℕ} {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {f : Vec d → E} (hf : Continuous f) : IntegrableOn f (FourierCalculus.closedCell d) :=
  hf.continuousOn.integrableOn_compact (FourierCalculus.isCompact_closedCell d)

theorem FourierCalculus.cell_integral_coordinate_sum {n : ℕ}
    {f : Vec (n + 1) → ℂ} (hf : ContDiff ℝ 1 f) :
    (∑ i : Fin (n + 1), ∫ x in unitCell (n + 1), ‖coordDeriv i f x‖ ^ 2) =
      ∫ x in unitCell (n + 1),
        ∑ i : Fin (n + 1), ‖coordDeriv i f x‖ ^ 2 := by
  have hInt : ∀ i : Fin (n + 1),
      IntegrableOn (fun x : Vec (n + 1) => ‖coordDeriv i f x‖ ^ 2)
        (unitCell (n + 1)) := by
    intro i
    have hcont : Continuous (fun x : Vec (n + 1) => ‖coordDeriv i f x‖ ^ 2) :=
      (continuous_coordDeriv i hf).norm.pow 2
    have hclosed := FourierCalculus.continuous_integrableOn_closedCell hcont
    have hsubset : unitCell (n + 1) ⊆ FourierCalculus.closedCell (n + 1) := by
      intro x hx
      simp only [unitCell, unitCellAt, Set.mem_ofPred_eq, zero_add] at hx
      simp only [FourierCalculus.closedCell, Set.mem_pi, mem_univ, forall_true_left]
      intro j
      exact ⟨le_of_lt (hx j).1, (hx j).2⟩
    exact hclosed.mono_set hsubset
  have hsum := MeasureTheory.integral_finsetSum
    (Finset.univ : Finset (Fin (n + 1)))
    (μ := (volume : Measure (Vec (n + 1))).restrict (unitCell (n + 1)))
    (f := fun i : Fin (n + 1) => fun x : Vec (n + 1) => ‖coordDeriv i f x‖ ^ 2)
    (fun i _hi => hInt i)
  simpa using hsum.symm

theorem integral_unitCell_gradSq_eq_sum_coord {n : ℕ}
    {f : Vec (n + 1) → ℂ} (hf : ContDiff ℝ 1 f) :
    (∑ i : Fin (n + 1), ∫ x in unitCell (n + 1), ‖coordDeriv i f x‖ ^ 2) =
      ∫ x in unitCell (n + 1),
        ∑ i : Fin (n + 1), ‖coordDeriv i f x‖ ^ 2 :=
  FourierCalculus.cell_integral_coordinate_sum hf

                                                                  
                                                   
                                                     
                                                                            
      
                                         
                                                              
                                                       
                 
          

                                                                       
                                                                      
                           
                                                                      
                                                              
                                          
      
                                                                    
                          
                                                                                
                                
                
                                                   
                                                                                   
                                                                
                                          
          
                              
                                                                                    
                                    
                    
              
                               
                                                                                 
                             
                               
                                                                                     
                             
                                                                    
                                              
              

                                                                           
                                                             
           
                                         
                                   
                                         
         
                                                              
                                                                 
                                                                    
                                     
                                                                    
                                                            
                      

                                                                   
                           
                                                                                   
                                           
                               

                                                                          
                                                                      
                                                                      
                                                
                                                
                                        
                           
                                
                                                         
                                                                        
                                           
                                                                  
                                                       
                                                    
                                                                   
                                                            
               
                                                                           
           
                       
             
                        
                
                                                            
                                                                                        
                                                    
                                                                    
                                     
                                                                      
            
                                                            
                                                                       
                                                 
                 
                                                            
                                                                    
                                                
                                                       
                                           
                             
                                                                          
          
                                      
                                 
                                                                      
                                        
                                 
                                                                       
                                                   
                                                                           
                                 
                                                                                    
                                
                                                    
                                                               
                                           
                                                 
                         

end AVenhance.Infra.Torus
