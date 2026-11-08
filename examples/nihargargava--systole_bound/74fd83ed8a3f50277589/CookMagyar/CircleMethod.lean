module

/-
Copyright (c) 2026.
Released under Apache 2.0 license.

The additive-character and interval-orthogonality proofs in this file are
adapted from Gershon Bialer's `ternary-goldbach-lean`,
`MathExtras.NumberTheory.Vinogradov.CircleMethod` (Apache-2.0).  The
arbitrary-arity cubic coefficient extraction is new to this project.
-/
public import Mathlib.Analysis.Fourier.AddCircle
public import Mathlib.Analysis.SpecialFunctions.Complex.Circle
public import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
public import Mathlib.Tactic

@[expose] public section

open MeasureTheory
open scoped ArithmeticFunction BigOperators

namespace SystolicGrowth

/-! # Exact circle-method identities for `x^3 - x`

This file contains the algebraic and Fourier-analytic part of the
Cook--Magyar specialization.  There are no asymptotic estimates here: the
main result, `integral_cubicVonMangoldtExpSum_pow`, is the exact identity
which turns a Fourier integral into the von-Mangoldt-weighted number of
representations of a target by `n` values of `x^3-x`.
-/

/-- The cubic polynomial used throughout the arithmetic construction. -/
def primeCubic (x : ℕ) : ℕ := x ^ 3 - x

namespace CookMagyarCircle

/-- The additive character `e(kα) = exp(2πikα)`. -/
noncomputable def addChar (α : ℝ) (k : ℕ) : ℂ :=
  Complex.exp (2 * Real.pi * Complex.I * (k : ℂ) * (α : ℂ))

/-- The negative-frequency character `e(-kα)`. -/
noncomputable def negAddChar (α : ℝ) (k : ℕ) : ℂ :=
  Complex.exp (-2 * Real.pi * Complex.I * (α : ℂ) * (k : ℂ))

                                                                 
                

                                                                  
                

                                                                       
                   

                                                                        
                   

                                                                      
                
          
                                                   
                                                         
             
        
                                       

                                                                            
                   
          
                                                    
                                                          
             
        
                                       

                                                                        
                                       
                                                       
                
                        
         
           
      

                                                                      
                                                                 
                                                     
           
                            
                                                               
           
                                              
                   
                          
                                                                         
                             

                                                          
theorem integral_exp_int_frequency (k : ℤ) :
    ∫ α in Set.Icc (0 : ℝ) 1,
        Complex.exp (2 * Real.pi * Complex.I * (k : ℂ) * (α : ℂ)) =
      if k = 0 then 1 else 0 := by
  by_cases hk : k = 0
  · simp [hk]
  · have hcoeff_zero :
        fourierCoeffOn (a := (0 : ℝ)) (b := 1) zero_lt_one
          (fun _ : ℝ ↦ (1 : ℂ)) (-k) = 0 := by
      have h := fourierCoeffOn_of_hasDerivAt (hab := zero_lt_one)
        (n := -k) (hn := neg_ne_zero.mpr hk)
        (f := fun _ : ℝ ↦ (1 : ℂ)) (f' := fun _ : ℝ ↦ (0 : ℂ))
        (by
          intro x _hx
          simpa using (hasDerivAt_const (x := x) (c := (1 : ℂ))))
        (by
          simp : IntervalIntegrable (fun _ : ℝ ↦ (0 : ℂ)) volume (0 : ℝ) 1)
      have hz :
          fourierCoeffOn (a := (0 : ℝ)) (b := 1) zero_lt_one
            (fun _ : ℝ ↦ (0 : ℂ)) (-k) = 0 := by
        rw [fourierCoeffOn_eq_integral]
        simp
      rw [hz] at h
      simpa using h
    have hcoeff_int := fourierCoeffOn_eq_integral (a := (0 : ℝ)) (b := 1)
      (f := fun _ : ℝ ↦ (1 : ℂ)) (-k) zero_lt_one
    simp only [sub_zero, one_div, inv_one, one_smul] at hcoeff_int
    rw [intervalIntegral.integral_of_le zero_le_one] at hcoeff_int
    rw [← integral_Icc_eq_integral_Ioc] at hcoeff_int
    have hint_zero :
        ∫ x in Set.Icc (0 : ℝ) 1, fourier k (x : AddCircle (1 : ℝ)) = 0 := by
      simpa [hk] using hcoeff_int.symm.trans hcoeff_zero
    rw [if_neg hk]
    convert hint_zero using 2
    ext x
    rw [fourier_coe_apply]
    push_cast
    ring_nf

/-- Orthogonality in the natural-number frequency convention used below. -/
theorem integral_addChar_mul_negAddChar (m n : ℕ) :
    ∫ α in Set.Icc (0 : ℝ) 1, addChar α m * negAddChar α n =
      if m = n then 1 else 0 := by
  have horth := integral_exp_int_frequency ((m : ℤ) - (n : ℤ))
  have hif :
      (if ((m : ℤ) - (n : ℤ) : ℤ) = 0 then (1 : ℂ) else 0) =
        if m = n then 1 else 0 := by
    split_ifs with h hmn hmn
    · rfl
    · omega
    · omega
    · rfl
  rw [hif] at horth
  rw [← horth]
  apply integral_congr_ae
  filter_upwards with α
  unfold addChar negAddChar
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring_nf

                                                                           
                                                          
                                                               
                    
                                                                     

                                               
                                                  
                                    
                                           

                                      
                                            
                                                
                      
                            
                                                                       

                                                  
                                       
         
                                                    
                                         
                                      
                                               
                              
                    
                                    
           
     

                                                                            
                                                                          
                                                         
                             
                                                           
                                                      
           
                        
                                                         
                                  
                                          
                                                                      
           
                                                
                                      
                       
                              
               
        
                                                                     
                         
                                       
             
                              
               
            
                                  
                                            
                                                                     
                                          
                                     
                                                                   
                                                   
                                                 
                                         
                                                   
                                        
                          
               
                                     
                             
            

                                                                         
                                                           
                                                  
           
                                                              
                                      
             
                                                                              
                  

                                                                   
                                                                      
                                           
                                                         
                            
                                                           

                                                        
                               
                                                                  
           
             
             
                                                         
                                                                      
                                              
                                                     
                                                   
                                      
                                                                                    
           
                                 
                                   
                                                      

                                                                    
                                                     
                                                            
                                              
                                                 
           
                                                                       
                                           
                                                                                   
           
             
                                                                              
                  
                                                           
                                       
             
                  
                                              
                         
                                                                          
                                                       
                      
                       
                  
                                                
                                               
                           

end CookMagyarCircle
end SystolicGrowth
