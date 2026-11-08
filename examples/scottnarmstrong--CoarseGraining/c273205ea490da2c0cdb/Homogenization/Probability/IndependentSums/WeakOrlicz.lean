import Mathlib
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.MeasureTheory.Measure.Real

namespace Homogenization
namespace IndependentSums

open MeasureTheory

variable {Ω : Type*}

/-!
Weak-Orlicz tail notation for the independent-sums probability mini-library.

This file follows the Chapter 4 note-facing convention directly:

- `X ≤ O_Ψ(A)` means `P[X > A t] ≤ Ψ(t)⁻¹` for every `t ≥ 1`;
- `X = O_Ψ(A)` means the same bound for `|X|`;
- `Γ_σ` and `Ψ_σ` are the stretched-exponential and log-normal model classes.

The definitions are intentionally tail-based rather than Banach-space based:
the notes use a weak-tail calculus, and this is the theorem surface needed for
the later concentration arguments.
-/

/-- The upper-tail event `{X > a}`. -/
def upperTailEvent (X : Ω → ℝ) (a : ℝ) : Set Ω :=
  {ω | a < X ω}

                                                 
                                               
                                   

                                                                
                                       
         

                                                              
                                       
         

                                                                       
                                                 
            
              
                             

                                                                     
                                          
                                                     

variable [MeasurableSpace Ω]

/-- The weak-Orlicz upper-tail relation `X ≤ O_Ψ(A)` from the notes. -/
def IsBigOWith (μ : Measure Ω) (Ψ : ℝ → ℝ) (X : Ω → ℝ) (A : ℝ) : Prop :=
  ∀ ⦃t : ℝ⦄, 1 ≤ t → μ.real (upperTailEvent X (A * t)) ≤ (Ψ t)⁻¹

/-- The symmetric weak-Orlicz relation `X = O_Ψ(A)`, defined through `|X|`. -/
def IsBigO (μ : Measure Ω) (Ψ : ℝ → ℝ) (X : Ω → ℝ) (A : ℝ) : Prop :=
  IsBigOWith μ Ψ (fun ω => |X ω|) A

                                                                    
                                                              
                                       
                                                       

theorem IsBigOWith.of_le {μ : Measure Ω} [IsFiniteMeasure μ] {Ψ : ℝ → ℝ}
    {X Y : Ω → ℝ} {A : ℝ}
    (hX : IsBigOWith μ Ψ X A) (hYX : ∀ ω, Y ω ≤ X ω) :
    IsBigOWith μ Ψ Y A := by
  intro t ht
  refine (measureReal_mono ?_).trans (hX ht)
  intro ω hω
  exact lt_of_lt_of_le hω (hYX ω)

theorem IsBigO.of_abs_le {μ : Measure Ω} [IsFiniteMeasure μ] {Ψ : ℝ → ℝ}
    {X Y : Ω → ℝ} {A : ℝ}
    (hX : IsBigO μ Ψ X A) (hYX : ∀ ω, |Y ω| ≤ |X ω|) :
    IsBigO μ Ψ Y A :=
  hX.of_le hYX

                                                                             
                         
                                             
                            
            
                                             
                                            
                                                                      

                                                                         
                         
                                         
                        
                                                                     
                            

                                                        
                                      
                               
                                                   
                      
              
                                        
                                                                             
                                      
                                                 
                                                          
              
               
                                                                                        
           
                 
                
                                            
                                              
                                    
                                          
                
                                      
                                               
                                                
                                    
             
               

                                                    
                                      
                           
                                               
                                                 
                                                                                        

theorem IsBigO.neg {μ : Measure Ω} [IsFiniteMeasure μ] {Ψ : ℝ → ℝ} {X : Ω → ℝ}
    {A : ℝ}
    (hX : IsBigO μ Ψ X A) :
    IsBigO μ Ψ (fun ω => -X ω) A := by
  exact hX.of_abs_le fun ω => by simp

                                                                         
                                               
                           

                                      
                                          
                                             
                                                                        

                                            
                                        
     

                                          
                                                                                   
     

                                          
                                                  
                                 

                                        
                      
                                                                            
                               

                                                  
                            
                                                
                                                   

                                   
                          
                                                                          
                                                                 
                                                 

                                                    
                                               
                     
                                                         

                                                       
                                      
                                       
            
                            

                                                  
                                             
                     
                                      
                                                   
            
                                      
                                                   
            
                                      
                                                   
            
                                      
                                                   
            
                                           
                                                    
                                                          
                
                                                       
                                          
                                                                           
                                                                           
                
                                                                               
             
                              
                                                                    

                                                     
                                    
                                     
            
                       

                                                                         
                                     
                        
                                                                     
             
                
                                                 
                
                                                 

                                                                     
                                 
                        
                                                                   
             
                
                                                                                   
                
                                                                                   

                                                                       
                                   
                        
                                           
                                                                                
             
                
                                               
                
                                               

                                                                   
                               
                        
                                         
                                                                                
             
                
                                                                                 
                
                                                                                 

end IndependentSums
end Homogenization
