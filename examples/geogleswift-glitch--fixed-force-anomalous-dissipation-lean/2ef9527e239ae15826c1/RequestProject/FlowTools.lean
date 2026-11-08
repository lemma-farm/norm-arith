module

public import RequestProject.FlowBasic

/-!
# Analytic tools for differentiating flows

A Grönwall estimate in closed form, a radial truncation, global existence for linear ODEs on a
compact time interval, a first-order Taylor estimate, and a criterion for Fréchet
differentiability from a quadratic remainder bound.
-/

@[expose] public section

open MeasureTheory Set Filter Topology Real Asymptotics
open scoped NNReal

noncomputable section

namespace AnomDiss

/-- Grönwall's inequality in closed form. -/
lemma gronwallBound_le {δ K ε x : ℝ} (hK : 0 ≤ K) (hε : 0 ≤ ε) :
    gronwallBound δ K ε x ≤ (δ + ε * x) * Real.exp (K * x) := by
  rcases eq_or_lt_of_le hK with h | h
  · subst h; simp [gronwallBound_K0]
  · rw [gronwallBound_of_K_ne_0 h.ne']
    have h1 : Real.exp (K * x) - 1 ≤ K * x * Real.exp (K * x) := by
      have := Real.add_one_le_exp (-(K * x))
      have h2 : Real.exp (-(K * x)) * Real.exp (K * x) = 1 := by
        rw [← Real.exp_add]; simp
      nlinarith [Real.exp_pos (K * x)]
    calc δ * Real.exp (K * x) + ε / K * (Real.exp (K * x) - 1)
        ≤ δ * Real.exp (K * x) + ε / K * (K * x * Real.exp (K * x)) := by gcongr
      _ = (δ + ε * x) * Real.exp (K * x) := by field_simp

/-- Grönwall's inequality for a function with an affine bound on its right derivative. -/
lemma norm_le_of_deriv_le {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f f' : ℝ → F} {a b K ε δ : ℝ} (hab : a ≤ b) (hK : 0 ≤ K) (hε : 0 ≤ ε)
    (hd : ∀ s ∈ Icc a b, HasDerivWithinAt f (f' s) (Icc a b) s)
    (hb : ∀ s ∈ Icc a b, ‖f' s‖ ≤ K * ‖f s‖ + ε) (h0 : ‖f a‖ ≤ δ) :
    ‖f b‖ ≤ (δ + ε * (b - a)) * Real.exp (K * (b - a)) := by
  have hc : ContinuousOn f (Icc a b) := fun s hs => (hd s hs).continuousWithinAt
  have hd' : ∀ s ∈ Ico a b, HasDerivWithinAt f (f' s) (Ici s) s := fun s hs => by
    have := hd s (Ico_subset_Icc_self hs)
    refine (this.mono_of_mem_nhdsWithin ?_)
    exact Icc_mem_nhdsGE_of_mem ⟨hs.1, hs.2⟩
  have := norm_le_gronwallBound_of_norm_deriv_right_le hc hd' h0
    (fun s hs => hb s (Ico_subset_Icc_self hs)) b ⟨hab, le_rfl⟩
  exact this.trans (gronwallBound_le hK hε)

/-- A version with `HasDerivAt` on the interval. -/
lemma norm_le_of_hasDerivAt_le {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f f' : ℝ → F} {a b K ε δ : ℝ} (hab : a ≤ b) (hK : 0 ≤ K) (hε : 0 ≤ ε)
    (hd : ∀ s ∈ Icc a b, HasDerivAt f (f' s) s)
    (hb : ∀ s ∈ Icc a b, ‖f' s‖ ≤ K * ‖f s‖ + ε) (h0 : ‖f a‖ ≤ δ) :
    ‖f b‖ ≤ (δ + ε * (b - a)) * Real.exp (K * (b - a)) :=
  norm_le_of_deriv_le hab hK hε (fun s hs => (hd s hs).hasDerivWithinAt) hb h0

/-! ### Radial truncation -/

                                                                
                                                                                      
                     

section Trunc

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

                                                                       
               
                                                    
                                     
                                                    

                                                                                  
               
                                                    
                                          
                                                                       
                                                      
                                    
                                                                    
                                                                                       

                                                                            
                                               

                                                                           
                                                

                                                                       
                                                 
                                                    
                                             
            
                                                   
                                 
                                                 
                                      
                           
                           
                                                          
                                       
                                                          
                                         
                               
                         
                                                                 
                                          
                               
                         
                                                                 
                                                                                
                                                                        
                                                        
         
                                                         
                                                            
                                                                                           
                                            
                                                                                         
                                      
                                                         

                                                                                 
                                                   
                                 
                                    
                                      
                                                                         

end Trunc

/-! ### Linear ODEs -/

                                                                                            
                                                                                         
                                                                                               
                                                                                   
                                                         
                                                                  
                                                                 
                                                                              
                                                     
                                        
                                                                                              
                                                        
                                                            
                                                                        
                                                             
                                                                   
                                                                                 
                                                    
                                                     
                                               
                                      
                                                                                    
                                                       
                                     
                                                                              
                                          
                                                       
                                             
                                                                                 
          
                                                            
                                         
                                                       
                                                                          
                                         
                                                                         
                                                                                       
                                                              
                          
                                        
              
                                                                                 
                       
           
                                                    
                                              
                                                                     
                                                                             
                                                                                        
                                      
                                                                 
                                 
                                    
                
            

                                                 

section Taylor

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]
  [NormedSpace ℝ F]

/-- First-order Taylor estimate from a Lipschitz derivative. -/
lemma norm_taylor1_le {f : E → F} {L : ℝ} (hL0 : 0 ≤ L) (hf : Differentiable ℝ f)
    (hL : ∀ a b, ‖fderiv ℝ f b - fderiv ℝ f a‖ ≤ L * ‖b - a‖) (a b : E) :
    ‖f b - f a - fderiv ℝ f a (b - a)‖ ≤ L * ‖b - a‖ ^ 2 := by
  set g : E → F := fun z => f z - fderiv ℝ f a z with hg
  have hgd : ∀ z, HasFDerivAt g (fderiv ℝ f z - fderiv ℝ f a) z := fun z =>
    (hf z).hasFDerivAt.sub (fderiv ℝ f a).hasFDerivAt
  have key := (convex_segment a b).norm_image_sub_le_of_norm_fderiv_le (f := g)
    (C := L * ‖b - a‖) (fun z _ => (hgd z).differentiableAt) (fun z hz => by
      rw [(hgd z).fderiv]
      refine (hL a z).trans ?_
      have hd := dist_add_dist_of_mem_segment hz
      rw [dist_eq_norm, dist_eq_norm, dist_eq_norm] at hd
      have : ‖z - a‖ ≤ ‖b - a‖ := by
        rw [norm_sub_rev z a, norm_sub_rev b a]; linarith [norm_nonneg (z - b)]
      exact mul_le_mul_of_nonneg_left this hL0)
    (left_mem_segment ℝ a b) (right_mem_segment ℝ a b)
  have he : g b - g a = f b - f a - fderiv ℝ f a (b - a) := by
    simp only [hg, map_sub]; abel
  rw [← he]
  calc ‖g b - g a‖ ≤ L * ‖b - a‖ * ‖b - a‖ := key
    _ = L * ‖b - a‖ ^ 2 := by ring

/-- A Lipschitz bound from a bound on the derivative. -/
lemma norm_sub_le_of_fderiv_le {f : E → F} {C : ℝ} (hf : Differentiable ℝ f)
    (hC : ∀ x, ‖fderiv ℝ f x‖ ≤ C) (a b : E) : ‖f b - f a‖ ≤ C * ‖b - a‖ :=
  convex_univ.norm_image_sub_le_of_norm_fderiv_le (fun z _ => hf z) (fun z _ => hC z)
    (mem_univ _) (mem_univ _)

/-- Fréchet differentiability from a quadratic remainder bound. -/
lemma hasFDerivAt_of_sq_bound {f : E → F} {f' : E →L[ℝ] F} {x : E} {C : ℝ}
    (h : ∀ y, ‖f y - f x - f' (y - x)‖ ≤ C * ‖y - x‖ ^ 2) : HasFDerivAt f f' x := by
  rw [hasFDerivAt_iff_isLittleO_nhds_zero]
  have h1 : (fun h => f (x + h) - f x - f' h) =O[𝓝 0] (fun h : E => ‖h‖ ^ 2) :=
    IsBigO.of_bound C (Eventually.of_forall fun v => by
      have := h (x + v)
      simp only [add_sub_cancel_left] at this
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      exact this)
  exact h1.trans_isLittleO (isLittleO_norm_pow_id one_lt_two)

end Taylor

                                                                                       
                                                                                      
                                                                   
                                                                       
                                       
                                                 
                                                                       
                                           

end AnomDiss
