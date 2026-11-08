/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.MarkovChain.Martingale
public import Mathlib
/-! # Increments of a harmonic function along a finite chain -/

@[expose] public section

namespace Rhone.MarkovChain.FinChain

open MeasureTheory ProbabilityTheory Finset Filter
open scoped NNReal

variable {S : Type*} [Fintype S] [MeasurableSpace S] [DiscreteMeasurableSpace S] (C : FinChain S)

omit [MeasurableSpace S] [DiscreteMeasurableSpace S] in
theorem abs_le_sum_abs (g : S → ℝ) (y : S) : |g y| ≤ ∑ z, |g z| :=
  Finset.single_le_sum (f := fun z => |g z|) (fun _ _ => abs_nonneg _) (Finset.mem_univ y)

theorem integral_mul_eval_succ (x : S) (n : ℕ) (g : S → ℝ) {h : (ℕ → S) → ℝ}
    (hh : StronglyMeasurable[Filtration.piLE (X := fun _ : ℕ => S) n] h) {B : ℝ}
    (hB : ∀ ω, |h ω| ≤ B) :
    ∫ ω, h ω * g (ω (n + 1)) ∂C.pathLaw x = ∫ ω, h ω * C.expect g (ω n) ∂C.pathLaw x := by
  have hle : Filtration.piLE (X := fun _ : ℕ => S) n ≤
      (inferInstance : MeasurableSpace (ℕ → S)) := Filtration.piLE.le n
  have hgm : Measurable fun ω : ℕ → S => g (ω (n + 1)) :=
    (Measurable.of_discrete (f := g)).comp (measurable_pi_apply _)
  have hint_g : Integrable (fun ω : ℕ → S => g (ω (n + 1))) (C.pathLaw x) :=
    C.integrable_eval g (n + 1) x
  have hint_hg : Integrable (h * fun ω : ℕ → S => g (ω (n + 1))) (C.pathLaw x) := by
    refine Integrable.of_bound ((hh.mono hle).mul hgm.stronglyMeasurable).aestronglyMeasurable
      (B * ∑ z, |g z|) (Eventually.of_forall fun ω => ?_)
    rw [Pi.mul_apply, Real.norm_eq_abs, abs_mul]
    exact mul_le_mul (hB ω) (abs_le_sum_abs g _) (abs_nonneg _) ((abs_nonneg _).trans (hB ω))
  have h1 := integral_condExp (μ := C.pathLaw x)
    (f := h * fun ω : ℕ → S => g (ω (n + 1))) hle
  have h2 := condExp_mul_of_stronglyMeasurable_left (μ := C.pathLaw x) hh hint_hg hint_g
  have h3 : (C.pathLaw x)[fun ω : ℕ → S => g (ω (n + 1)) | Filtration.piLE n] =ᵐ[C.pathLaw x]
      fun ω => ∫ y, g y ∂C.kernel (ω n) :=
    C.toProcess.condExp_eval_succ x n (Measurable.of_discrete (f := g)) (abs_le_sum_abs g)
  calc ∫ ω, h ω * g (ω (n + 1)) ∂C.pathLaw x
      = ∫ ω, (C.pathLaw x)[h * fun ω : ℕ → S => g (ω (n + 1)) | Filtration.piLE n] ω
          ∂C.pathLaw x := h1.symm
    _ = ∫ ω, h ω * C.expect g (ω n) ∂C.pathLaw x := by
        refine integral_congr_ae ?_
        filter_upwards [h2, h3] with ω hω2 hω3
        rw [hω2, Pi.mul_apply, hω3, C.integral_kernel]

                                               
                                                                                    
                                                                       
                                                                                          
                                                          
                                                                                           
                                                                     
                                                 

                                                                  
                                                                         
                                                                   
                                                   
                                                                          
                                                      
                                                                             
                                                                                      

                   
                                                                                   
                                                               
                                          
                                                                              
                                                                                       
                                                          
                                                               
                                                               
                                                                                                
                                                          
                                                                

theorem integral_mul_eval_succ_two (x : S) (n : ℕ) (G : S → S → ℝ) {h : (ℕ → S) → ℝ}
    (hh : StronglyMeasurable[Filtration.piLE (X := fun _ : ℕ => S) n] h) {B : ℝ}
    (hB : ∀ ω, |h ω| ≤ B) :
    ∫ ω, h ω * G (ω n) (ω (n + 1)) ∂C.pathLaw x =
      ∫ ω, h ω * C.expect (G (ω n)) (ω n) ∂C.pathLaw x := by
  classical
  have hle : Filtration.piLE (X := fun _ : ℕ => S) n ≤
      (inferInstance : MeasurableSpace (ℕ → S)) := Filtration.piLE.le n
  have hB0 : 0 ≤ B := by
    obtain ⟨ω⟩ : Nonempty (ℕ → S) := ⟨fun _ => x⟩
    exact (abs_nonneg _).trans (hB ω)
  have hind : ∀ z : S, StronglyMeasurable[Filtration.piLE (X := fun _ : ℕ => S) n]
      (fun ω : ℕ → S => h ω * (if ω n = z then 1 else 0)) := fun z =>
    hh.mul ((Measurable.of_discrete (f := fun y : S => if y = z then (1 : ℝ) else 0)).comp
      (DiscreteProcess.measurable_eval_piLE (S := S) n)).stronglyMeasurable
  have hindB : ∀ z ω, |h ω * (if ω n = z then (1 : ℝ) else 0)| ≤ B := by
    intro z ω
    split_ifs
    · simpa using hB ω
    · simpa using hB0
  have hsplit : ∀ (F : S → ℝ) (ω : ℕ → S), (∑ z, (h ω * (if ω n = z then 1 else 0)) * F z) =
      h ω * F (ω n) := by
    intro F ω
    rw [Finset.sum_eq_single (ω n)]
    · simp
    · intro z _ hz
      simp [Ne.symm hz]
    · simp
  have hint : ∀ (z : S) (F : (ℕ → S) → ℝ), Measurable F → (∀ ω, |F ω| ≤ ∑ y, |G z y|) →
      Integrable (fun ω => (h ω * (if ω n = z then 1 else 0)) * F ω) (C.pathLaw x) := by
    intro z F hFm hFb
    refine Integrable.of_bound (((hind z).mono hle).mul hFm.stronglyMeasurable).aestronglyMeasurable
      (B * ∑ y, |G z y|) (Eventually.of_forall fun ω => ?_)
    rw [Real.norm_eq_abs, abs_mul]
    exact mul_le_mul (hindB z ω) (hFb ω) (abs_nonneg _) hB0
  have hexp : ∀ (z y : S), |C.expect (G z) y| ≤ ∑ y, |G z y| := by
    intro z y
    rw [expect_apply]
    calc |∑ w, C.P y w * G z w| ≤ ∑ w, |C.P y w * G z w| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ w, |G z w| := by
          refine Finset.sum_le_sum fun w _ => ?_
          rw [abs_mul, abs_of_nonneg (C.nonneg y w)]
          have hP1 : C.P y w ≤ 1 := by
            rw [← C.row_sum y]
            exact Finset.single_le_sum (f := fun w => C.P y w) (fun w _ => C.nonneg y w)
              (Finset.mem_univ w)
          exact mul_le_of_le_one_left (abs_nonneg _) hP1
  have eL : (fun ω : ℕ → S => h ω * G (ω n) (ω (n + 1))) =
      fun ω => ∑ z, (h ω * (if ω n = z then 1 else 0)) * G z (ω (n + 1)) := by
    funext ω
    exact (hsplit (fun z => G z (ω (n + 1))) ω).symm
  have eR : (fun ω : ℕ → S => h ω * C.expect (G (ω n)) (ω n)) =
      fun ω => ∑ z, (h ω * (if ω n = z then 1 else 0)) * C.expect (G z) (ω n) := by
    funext ω
    exact (hsplit (fun z => C.expect (G z) (ω n)) ω).symm
  rw [eL, eR, integral_finsetSum _ fun z _ => hint z (fun ω => G z (ω (n + 1)))
      ((Measurable.of_discrete (f := G z)).comp (measurable_pi_apply _))
      (fun ω => abs_le_sum_abs (G z) _),
    integral_finsetSum _ fun z _ => hint z (fun ω => C.expect (G z) (ω n))
      ((Measurable.of_discrete (f := C.expect (G z))).comp (measurable_pi_apply _))
      (fun ω => hexp z _)]
  exact Finset.sum_congr rfl fun z _ => C.integral_mul_eval_succ x n (G z) (hind z) (hindB z)

                                                       
                                                      
                                                          
                                                                                                 

                                                                         

                                                                   
                                                     
                                                                                 
                               
      

                                                                   
                                                                                 
                                          
                           
                     
                   
                                                   

                                                             
                                                 
                                                                             
                                                    
                  
                       
                
                  
                                                                                                
                                                                     
                                                        
                                               
             
                    
          
               
                                   
                                                                        
                                                                  
                                                                                  
                                                                                                
                                                            
                 
                                                                                                 
               
                                   
            
                                                      
                                                                                          
                                                                            
                                                   
                                                                                                    
                                                      
                          
               
              
                                                                         
                                                                                                
                                                                               
                                                                                              
                                                                                   

                                                                   
                                                   
                                                         
                                                                             
                                                                                  
                        
                             
                     
                                                                              
                  
                       
                
                  
                                                                                                
                                                      
                                                                       
                                                            
                                                                
                                               
             
                    
                           
                                                
                                                              
                                                                     
                                                                   
                                                                                    
                        
                                                                                              
                                                                                        
                        
                                                                                          
               
                                                                                      
                                                                             
                                                      
                                                                                    
                                                       
                                                          
                                                                                         
                                                        
                                                          
                                                              
                                                                       
                                                           
                                                                                   
                                                                
                                                            
                                                                                               
                 
                                                                               
                                                                      
                                                                            
                  
                             
                                          
                                                                           
                
                 
                                                                            
                                                                            
                  
                             
                                          
                                                                           
                
                 
                                                                                              
                                                              
                                                                                          
             
                            
                                                                                  
               
                                   
            
                                   
                                                                                      
                             
             
                                                                                    
                        
                                                            
                                                      
                                                                                              
                    
                                                                                        
                                    
                                                                                         
                                      
                            
                                               
                     
                                                                                
                                        
                                                                               
             
                                                                              
                                                     
                                                                                               
                                                    
                                                                                 
                                     
                            
             
                           

                                                                           
                                                                                  
                                                          
                                                        
           
                      
                                                                   
                                                            
                                                                                              
                                    
                                                        
                                                                                    
                                                                                     
                                                 
                                                                       
                                       
                                                                                             
                                               
                                                       
                                                            
             
                                   
             
              
                                     
                                                                                
                                           
                                                                        
             
                                     
                   
                  
                                                                          
                                                  
                                                                                             
                                                                              
             
                   
                    
          
                                                  
                                                                            
                
                                                                                    
                
                                       
               
                            
                                                                                             
                                                                                          
                                                                              
                                                                         
                                                                                 
                    
                                                                                            
                                       
                                                              
                                                                     
                                                    
                                                                              
                                                                 
                                                 
               
                                                
                                                                      
                                                                           
                                                          
                                      
                                          
                     
                                                                     
                  
           
                                                                                  
                                                         
             
                                 
          
                                           
                                                                                          
                                                                                            
            
                                                
                                       
                                                                                             
                                                   
                                  
                                                                                     
                                                         
                                                                                    
                                                          
                                                          
                                                                                   
                                                                          
           
                                         
                                                                                 
                 
                                                    
                                                       
                                                                       
                                    
                                                                           
                           
                                                                      
                                                
                                                                        
                                                                                    
                                                                              
                                                         
              
                                                                               
                
                         
                                            
                                                                                              
                                                            
                         
                      
                      
                                                                                   
                                   
                                
                                      
                                                 
                                       
                      
                                       
                                                              
                                
                                                                                             
                                                                                            
                                          
             
                                                                                  

end Rhone.MarkovChain.FinChain
