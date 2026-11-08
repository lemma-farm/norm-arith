/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Statistics.Identifiability.ACComparisonBounds
public import Rhone.Statistics.Identifiability.IntegrablePanLaw
public import Rhone.Statistics.Identifiability.PanDiagonalSufficiency
public import Rhone.Statistics.Identifiability.PanRecombinationUniqueness
public import Mathlib
/-! # Volterra uniqueness and Gronwall bounds for the common-clock equations -/

@[expose] public section

open Set Filter MeasureTheory
open scoped Topology
namespace Rhone.Statistics.Identifiability

theorem commonClock_integral_gronwall_zero {h : ℝ → ℝ} {T K : ℝ}
    (hT : 0 ≤ T) (hi : IntervalIntegrable h volume 0 T)
    (hn : ∀ t ∈ Icc 0 T, 0 ≤ h t)
    (hb : ∀ t ∈ Icc 0 T, h t ≤ K * ∫ s in (0 : ℝ)..t, h s) :
    EqOn h (fun _ => 0) (Icc 0 T) := by
  intro t ht
  have his : IntervalIntegrable h volume 0 t :=
    hi.mono_set (by simpa only [uIcc_of_le hT, uIcc_of_le ht.1] using
      (Icc_subset_Icc le_rfl ht.2))
  have hF := his.absolutelyContinuousOnInterval_intervalIntegral (c := 0) (by simp)
  have hFd : ∀ᵐ x, x ∈ uIcc 0 t →
      HasDerivAt (fun y => ∫ s in (0 : ℝ)..y, h s) (h x) x := by
    filter_upwards [his.ae_hasDerivAt_integral] with x hx hxmem
    exact hx hxmem 0 (by simp)
  have hH : AbsolutelyContinuousOnInterval (fun x : ℝ => -K * x) 0 t :=
    (LipschitzWith.id.lipschitzOnWith.absolutelyContinuousOnInterval).const_mul (-K)
  have hHd : ∀ᵐ x, x ∈ uIcc 0 t → HasDerivAt (fun y : ℝ => -K * y) (-K) x := by
    filter_upwards with x hx
    simpa using (hasDerivAt_id x).const_mul (-K)
  have hbound : ∀ᵐ x, x ∈ uIcc 0 t →
      h x ≤ -(-K) * ∫ s in (0 : ℝ)..x, h s := by
    filter_upwards with x hx
    have hx' : x ∈ Icc 0 t := by simpa only [uIcc_of_le ht.1] using hx
    simpa using hb x ⟨hx'.1, hx'.2.trans ht.2⟩
  have hle := ac_comparison_upper (fun y => ∫ s in (0 : ℝ)..y, h s) h
    (fun x => -K * x) (fun _ => -K) 0 t ht.1 hF hH hFd hHd hbound
  simp only [intervalIntegral.integral_same, mul_zero, zero_mul] at hle
  have hnonneg : 0 ≤ ∫ s in (0 : ℝ)..t, h s :=
    intervalIntegral.integral_nonneg ht.1 (fun s hs => hn s ⟨hs.1, hs.2.trans ht.2⟩)
  have he : (∫ s in (0 : ℝ)..t, h s) = 0 := le_antisymm hle hnonneg
  have hh := hb t ht
  rw [he, mul_zero] at hh
  exact le_antisymm hh (hn t ht)

theorem commonClock_volterra_unique {K : ℝ → ℝ → ℝ} {b u v : ℝ → ℝ} {T M : ℝ}
    (hT : 0 ≤ T) (hu : ContinuousOn u (Icc 0 T)) (hv : ContinuousOn v (Icc 0 T))
    (hKi : ∀ t ∈ Icc 0 T, IntervalIntegrable (K t) volume 0 t)
    (hKb : ∀ t ∈ Icc 0 T, ∀ s ∈ Icc 0 t, |K t s| ≤ M)
    (huEq : ∀ t ∈ Icc 0 T, u t = b t + ∫ s in (0 : ℝ)..t, K t s * u s)
    (hvEq : ∀ t ∈ Icc 0 T, v t = b t + ∫ s in (0 : ℝ)..t, K t s * v s) :
    EqOn u v (Icc 0 T) := by
  have hcont : ContinuousOn (fun s => |u s - v s|) (Icc 0 T) :=
    (hu.sub hv).abs
  have hz := commonClock_integral_gronwall_zero hT
    (hcont.intervalIntegrable_of_Icc hT) (fun _ _ => abs_nonneg _) (K := M) ?_
  · intro t ht
    exact sub_eq_zero.mp (abs_eq_zero.mp (hz ht))
  intro t ht
  have hs : Icc 0 t ⊆ Icc 0 T := Icc_subset_Icc le_rfl ht.2
  have hui : IntervalIntegrable (fun s => K t s * u s) volume 0 t :=
    (hKi t ht).mul_continuousOn ((hu.mono hs).mono (by rw [uIcc_of_le ht.1]))
  have hvi : IntervalIntegrable (fun s => K t s * v s) volume 0 t :=
    (hKi t ht).mul_continuousOn ((hv.mono hs).mono (by rw [uIcc_of_le ht.1]))
  have he : u t - v t = ∫ s in (0 : ℝ)..t, K t s * (u s - v s) := by
    rw [huEq t ht, hvEq t ht]
    simp_rw [mul_sub]
    rw [intervalIntegral.integral_sub hui hvi]
    ring
  rw [he]
  calc
    |∫ s in (0 : ℝ)..t, K t s * (u s - v s)| ≤
        ∫ s in (0 : ℝ)..t, |K t s * (u s - v s)| :=
      by
        simpa only [Real.norm_eq_abs] using
          (intervalIntegral.norm_integral_le_integral_norm
            (f := fun s => K t s * (u s - v s)) ht.1)
    _ ≤ ∫ s in (0 : ℝ)..t, M * |u s - v s| := by
      apply intervalIntegral.integral_mono_on ht.1
      · simpa only [mul_sub] using (hui.sub hvi).abs
      · exact ((hcont.mono hs).intervalIntegrable_of_Icc ht.1).const_mul M
      · intro s hs'
        rw [abs_mul]
        exact mul_le_mul_of_nonneg_right (hKb t ht s hs') (abs_nonneg _)
    _ = M * ∫ s in (0 : ℝ)..t, |u s - v s| := intervalIntegral.integral_const_mul _ _

                                                                        
                                     
                                                   
                                                                                    
                                                  

                                        
                                                                       
                
                                                                       
                                                                       
                                                                         
                                          
                                        
                                                                  
                                         
                                                         
                                         
                                                         
                                         
                                                         
                                         
                                                           
                                                     
                                
                                
                                   
                                                     
                                                     
                                                           
                                                                 
                                                                          
                                                             
                                    
                                                                           
                                                                      
                                                         
                              
                                                        
                                                        
                                                          
                                                                                         
                                                        
                                         
              
                  
        
                                                                      
                                                         
                              
                                                        
                                        
        
                                                             
                                              
                                                          
                                                             
                                          
                                                    
                                                                     
                                                                                                    
                    
              
                                                                 
                                             
                                 
                              
                                                                                
                                                                                
                                       
                                                      
                                               
                                                                                 
                                                                        
              
                                                                             
                
                                 
                                                                                       
                                                                             
                
                                 
                                                                                       
                  
               
                                                     
                                             
             
              
                    
                           
                                                                                                
                                              
              
                    
                           
                                                                                                
                                              

                                                                        
                                                
                                                     
                                      
                                       
                                                       
                               
                                       
                                                    
                                                                                
                                              
                                         
              
        
         
          

                                            
                                                         
                                         
                                                                      
                                    
                                                                       
                                                                       
                                    
                                                  
                                    
                                                  
                                              
                                                                        
                                              
                                                                          
                                                     
                                             
                                       
                                           
                                        
                                                         
                                          
                                                                                  
                                                           
                                                            
                                                
                                                                          
                          
                                                                      
                                                                                          
                                                
                                                 
                                                                       
                                                             
                                                                       
                                                         
                                                                  
                               
                                                                                      
                                             
             
                                                                                 
                                                                      
                                    
                                                                                    
                                                        
                      
                   
                                                       
                                        
                                                     
                                                     
                                    
                                                     
                        
                                                     
                                                                                       
                            
                                           
               
                           
                                                                
                                   
               
                  
                                                  
                             
                                                                             
                                                       
                                        
                         
                         
                                          
                         
              
                                                    
              
                            
           
                                         
              
                
        
              
                                                    
              
                            
           
                                         
              
                
        

                                         
                                    
                                                                  
                                                                
                                                                   
                                                                   
                                                                               
                                                                               
                                            
                                                                        
                                            
                                                                          
                                                 
                                                                         
                                                               
                                                            
                                                                 
                                                                 
                                                     
                                                     
                                              
                                         

end Rhone.Statistics.Identifiability
