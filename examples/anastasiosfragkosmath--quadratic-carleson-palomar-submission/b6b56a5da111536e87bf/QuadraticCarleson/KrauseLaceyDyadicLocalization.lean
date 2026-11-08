/-
Copyright (c) 2026 Quadratic Carleson formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quadratic Carleson formalization contributors
-/
import QuadraticCarleson.KrauseLaceySparseInterface
import QuadraticCarleson.QuadraticFixedHeightAveragingAmplitude
import Mathlib
/-!
# Dyadic localization in the Krause--Lacey sparse recursion

This module formalizes the geometric localization at the start of Section 3
of Krause--Lacey, *Sparse bounds for maximal monomial oscillatory Hilbert
transforms* (arXiv:1609.01564).  In their display (3.2), an interval `I` of
length `2^(k+2)` is assigned a genuine dyadic kernel piece at scale `k`, and
the input is restricted to the central third `I'`.  The resulting piece is
supported in `I`.

The source first concentrates on the positive half-kernel `ρₖ⁺`, saying
explicitly that the complementary negative half is symmetric.  Accordingly,
our main localized piece uses the project's concrete `positiveDyadicAmplitude`;
a separate signed companion below uses the full `dyadicPsi` and connects this
localization to the genuine full dyadic Hilbert kernel.  Both have outer
support radius `2^(j-1)`, exactly one eighth of `2^(j+2)` in the project's
indexing.

The genuinely analytic input called Lemma 3.5 in that source is deliberately
not asserted here: it is the remaining local oscillatory `L¹ → L^q` estimate.
The results below prove its localization and stopping/packing framework, but
do not replace that estimate by an assumption.
-/

open Function MeasureTheory Set
open scoped ENNReal

namespace QuadraticCarleson

set_option autoImplicit false

/-- The interval `I'` in Krause--Lacey display (3.2): the central third of
`I`.  We retain the project's canonical half-open representative. -/
noncomputable def RealInterval.centralThird (I : RealInterval) : Set ℝ :=
  Ioc ((2 * I.left + I.right) / 3) ((I.left + 2 * I.right) / 3)

theorem RealInterval.measurableSet_centralThird (I : RealInterval) :
    MeasurableSet I.centralThird := measurableSet_Ioc

theorem RealInterval.centralThird_subset_carrier (I : RealInterval) :
    I.centralThird ⊆ I.carrier := by
  intro x hx
  change (2 * I.left + I.right) / 3 < x ∧
    x ≤ (I.left + 2 * I.right) / 3 at hx
  change I.left < x ∧ x ≤ I.right
  exact ⟨by linarith [hx.1, I.left_lt_right],
    by linarith [hx.2, I.left_lt_right]⟩

/-- The genuine localized quadratic dyadic piece corresponding to
Krause--Lacey (3.2), with the source input restriction to the central third.
The harmless phase parameter is left explicit. -/
noncomputable def krauseLaceyLocalizedPiece
    (lam : ℝ) (j : ℤ) (I : RealInterval) (f : ℝ → ℂ) (x : ℝ) : ℂ :=
  ∫ y, positiveDyadicAmplitude j y * phase (lam * y ^ 2) *
    I.centralThird.indicator f (x - y)

/-- At the source scale relation `|I| = 2^(j+2)`, the outer radius of the
project's one-sided dyadic amplitude is exactly `|I|/8`. -/
theorem krauseLacey_scale_eq_eight_mul_radius (j : ℤ) :
    (2 : ℝ) ^ (j + 2) = 8 * (2 : ℝ) ^ (j - 1) := by
  rw [show j + 2 = (j - 1) + 3 by ring,
    zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]
  norm_num
  ring

/-- The exact support/locality assertion following Krause--Lacey (3.2):
localizing the input to the central third makes the scale-`j` piece supported
on `I` whenever `|I| = 2^(j+2)`.

The statement is pointwise and needs no integrability hypothesis: outside
`I` the integrand vanishes identically. -/
theorem krauseLaceyLocalizedPiece_eq_zero_of_notMem
    (lam : ℝ) (j : ℤ) (I : RealInterval) (f : ℝ → ℂ)
    (hscale : I.length = (2 : ℝ) ^ (j + 2))
    {x : ℝ} (hx : x ∉ I.carrier) :
    krauseLaceyLocalizedPiece lam j I f x = 0 := by
  unfold krauseLaceyLocalizedPiece
  calc
    ∫ y, positiveDyadicAmplitude j y * phase (lam * y ^ 2) *
        I.centralThird.indicator f (x - y) = ∫ _y : ℝ, (0 : ℂ) := by
      apply integral_congr_ae
      filter_upwards with y
      by_cases ha : positiveDyadicAmplitude j y = 0
      · simp [ha]
      have hy := positiveDyadicAmplitude_support_subset j ha
      have hradius_pos : 0 < (2 : ℝ) ^ (j - 1) := zpow_pos (by norm_num) _
      have hy_nonneg : 0 ≤ y :=
        le_trans (div_nonneg hradius_pos.le (by norm_num)) hy.1
      have hy_upper : y ≤ I.length / 8 := by
        rw [hscale, krauseLacey_scale_eq_eight_mul_radius]
        norm_num
        exact hy.2
      have hnotmid : x - y ∉ I.centralThird := by
        intro hmid
        change (2 * I.left + I.right) / 3 < x - y ∧
          x - y ≤ (I.left + 2 * I.right) / 3 at hmid
        apply hx
        rw [RealInterval.carrier]
        constructor
        · change I.left < x
          linarith [hmid.1, I.left_lt_right]
        · change x ≤ I.right
          dsimp [RealInterval.length] at hy_upper
          linarith [hmid.2]
      rw [Set.indicator_of_notMem hnotmid]
      simp
    _ = 0 := by simp

                                                                      
                
                                                
                                                    
                                             
                                                                            
            
                
                                                                              

                                                                         
                                                                         
                                                                     
                                                 
                                                                   
                                                  
                                      

                                                         
                                                    
                                           
                                  
                                                         
                                        
      
                                                    
                                                                    
                             
                           
                                     
                 
                                              
                                                                    
                                            
                                                          
                
                                           
                                               
                                                          
                
                                                       
                                                 
                  
                                                   
                                                    
                
                                 
                   
                           
                                                 
                                            
                            
                                                 
                           
                                          
          
                    

                                                      
                                                    
                                             
                                                                                  
            
                
                                                                                    

                                                                           
                                    
noncomputable def intervalL1Average (f : ℝ → ℂ) (I : RealInterval) : ℝ :=
  I.length⁻¹ * ∫ x in I.carrier, ‖f x‖

theorem intervalL1Average_nonneg (f : ℝ → ℂ) (I : RealInterval) :
    0 ≤ intervalL1Average f I := by
  exact mul_nonneg (inv_nonneg.mpr I.length_pos.le) (integral_nonneg fun _ ↦ norm_nonneg _)

theorem intervalL1Average_mul_length (f : ℝ → ℂ) (I : RealInterval) :
    intervalL1Average f I * I.length = ∫ x in I.carrier, ‖f x‖ := by
  rw [intervalL1Average]
  field_simp [I.length_pos.ne']

                                                                       
                                                                          
                                                    

                                                                            
                                                                   
                                                    
                                                                        
               
                                                                   
                                               
                                   
                    
                                                               
                                               
           
                          
                                                                               
                
                                
                                                            
                  
                                                              
                                                    
                                            
                
          
                                                     
                                                       
                                                              
                                                                               
                                                                
                
                                  
                            
                               
                          
                  
                                              
                                       
                                     
                                                                 
                                        
                                                                                       
                  
                                                              
                                                
                                                       
                                    
                                                       
                                                          
                                                         
                                                      
                              
                       
                                                        
                                              
                                                                 
               
                                
                                                  

                                                                         
                                                                              
                                                                             
                                                                      
                                                    
                                                                        
                 
                                                                   
                                               
                                                                   
                    
                                                              
                                                                 
                                              
           
                             
                                                          
                                             
                                               
                    
              
                                     
                                                         
                                               
                    
              
                                     
                                                                    
                                                      
                                
                
                                              
              
                
                                       
                                                                                  
                                                      
                                            
                
                                              
              
                
                                                   
                                        
                                                                      
                           

                                                                            
                                                                         
                                  
                                                                                   
                                      

                                                    
                                                                          
                                                              
                                    
                                                                          

                                                                         
                                                                         
                                                                         
                                    
                                                              
                                                                        
                 
                                                                   
                                               
                                                                   
                    
                                                              
                                                                 
                      
                                                                  
           
                                                              
              
                                
                               
                       
                                                              
                                                                        
                       
                                                
                                   
                                                   
                                                                         
                                                    
                              
              
                                     
                                                            
                                   
                                     
                           
                                                      
                                                                       
                                                  
                                                      
                                                  
                                 
                                             
             
          

                                                                       
                                                       
                                                          
                                                                        
                 
                                                                   
                                               
                                                                   
                    
                                                              
                                                                 
                      
                                                                  
                                                                      
                                   
                           
          

                                                              

                                                                           
                                                                             
                                                                            
                                                                           
                                                                         
                                                                            
        
                                               
                                                                             
                                                         
                           
                                                     
                                                       
                                                                   
                                      
                                                          
                                                           
                                        
                                    
                                                   
                                                    
                                                  
           
                                                                      
                                                                
                                                      
           
                                                                            
           
                      
                 
                                  
             
                               
                                                              
                                                   
                                    
                               
                     
                     
                              
                                 
                                    
                               
                     
                     
                              
                                 
           
                                                            
                                                     
                                                                          
                                    

end QuadraticCarleson
