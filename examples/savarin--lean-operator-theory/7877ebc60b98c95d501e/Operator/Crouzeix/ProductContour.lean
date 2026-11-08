/-
# The separated Crouzeix--Palencia product contour

The pointwise polynomial resolvent splitting in `PalenciaSupport.lean` writes
the integrand for `p(A) G` as the difference of two terms.  To estimate those
terms separately, one first has to know that the divided-difference term
depends continuously on the boundary point.  This file proves that continuity
directly from Mathlib's coefficient formula

`coeff (p /ₘ (X - C z)) n = ∑ i, z ^ (i - n - 1) * coeff p i`,

then proves contour integrability of both terms and separates the contour
integral.  The resulting identity is exact, but its two terms are not
independently sharp: applying the triangle inequality loses the cancellation
needed for the `m²` product constant.  The separated form is therefore an
algebraic diagnostic and a possible input to a stronger coupled invariant,
not by itself a reduction to two attainable norm estimates.

## Main declarations

* `continuous_aeval_divByMonic_X_sub_C` -- continuity of the evaluated
  polynomial divided difference in its boundary point.
* `crouzeixProductMainIntegrand_contourIntegrable` and
  `crouzeixProductRemainderIntegrand_contourIntegrable` -- integrability of
  the two separated product-contour terms.
* `crouzeixProductRemainderPolynomial` and
  `normalized_crouzeixProductRemainderContour_eq_aeval` -- the remainder
  contour is polynomial functional calculus of degree strictly below that
  of a nonconstant input polynomial.
* `crouzeixProductRemainderPolynomial_smul` -- degree-two homogeneity of the
  remainder, its evaluated norm, and its polynomial sup norm under scaling.
* `crouzeixSquareAuxiliaryOperator_smul` -- matching degree-two homogeneity
  of the scalar-square main auxiliary operator.
* `aeval_mul_crouzeixPolynomialAuxiliaryOperator_eq_main_sub_remainder` --
  the exact separated contour identity for `p(A) G`.
* `aeval_mul_crouzeixPolynomialAuxiliaryOperator_eq_main_sub_aeval_remainderPolynomial`
  -- the same identity with the lower-degree remainder written as polynomial
  functional calculus.
* `aeval_mul_crouzeixPolynomialAuxiliaryOperator_eq_squareAux_sub_aeval_remainderPolynomial`
  -- the recursive form: a scalar-square auxiliary operator minus the
  lower-degree polynomial functional calculus.
* `norm_aeval_mul_crouzeixPolynomialAuxiliaryOperator_le_main_add_remainder`
  -- the corresponding two-term norm reduction.
-/
import Operator.Crouzeix.PalenciaSupport
import Mathlib

open Complex Polynomial Set
open scoped InnerProductSpace Interval Real

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-- The operator evaluation of the divided difference
`p /ₘ (X - C z)` depends continuously on `z`.

This is not an immediate application of continuity of polynomial evaluation,
because the polynomial itself varies with `z`.  Expanding every coefficient
of the quotient as a finite polynomial sum in `z` makes continuity explicit. -/
theorem continuous_aeval_divByMonic_X_sub_C
    (A : E →L[ℂ] E) (p : Polynomial ℂ) :
    Continuous (fun z : ℂ =>
      Polynomial.aeval A (p /ₘ (Polynomial.X - Polynomial.C z))) := by
  have hfun :
      (fun z : ℂ => Polynomial.aeval A
        (p /ₘ (Polynomial.X - Polynomial.C z))) =
      fun z => ∑ i ∈ Finset.range (p.natDegree + 1),
        (∑ j ∈ Finset.Icc (i + 1) p.natDegree,
          z ^ (j - (i + 1)) * p.coeff j) • A ^ i := by
    funext z
    rw [Polynomial.aeval_eq_sum_range' (x := A) (n := p.natDegree + 1)]
    · congr 1 with i
      rw [Polynomial.coeff_divByMonic_X_sub_C]
    · rw [Polynomial.natDegree_divByMonic p (Polynomial.monic_X_sub_C z),
        Polynomial.natDegree_X_sub_C]
      omega
  rw [hfun]
  fun_prop

/-- Every coefficient of the polynomial divided difference depends
continuously on its boundary point. -/
theorem continuous_coeff_divByMonic_X_sub_C (p : Polynomial ℂ) (n : ℕ) :
    Continuous (fun z : ℂ =>
      (p /ₘ (Polynomial.X - Polynomial.C z)).coeff n) := by
  have hfun :
      (fun z : ℂ => (p /ₘ (Polynomial.X - Polynomial.C z)).coeff n) =
      fun z => ∑ i ∈ Finset.Icc (n + 1) p.natDegree,
        z ^ (i - (n + 1)) * p.coeff i := by
    funext z
    rw [Polynomial.coeff_divByMonic_X_sub_C]
  rw [hfun]
  fun_prop

                                           
                                          
                                                                      
                                                       
                                                        
             
                                                                                      
             
                                                                      
                               
         
                
             
                                           
                                                                
                                                                                      
                                           
                                                              

                                                          
                                                                         
                                                         
                                   
                                            
            
                                                              
                                       
                        
                                             
                                                      
                                                             
                                               
                                                                    
                                                                                          
                                                                          
                                                             
                                               
                                                                    
                                                                                          
                                                  
                                                                     
                                                                  
                                                    
                  
                                    
              
                                                                               
                 
                                                          
                                    
                
                                 
                                                               

                                                                      
                                                                       
                          
theorem crouzeixProductMainIntegrand_contourIntegrable [CompleteSpace E]
    (A : E →L[ℂ] E) (Omega : SmoothJordanDomain) (p : Polynomial ℂ)
    (hOmega : closure (numericalRange A) ⊆ Omega.carrier) :
    ContourIntegrable
      (fun z => (star (Polynomial.eval z p) * Polynomial.eval z p) •
        resolvent A z) Omega.boundaryParam := by
  exact crouzeixAuxiliaryIntegrand_contourIntegrable A Omega
    (fun z => star (Polynomial.eval z p) * Polynomial.eval z p) hOmega
    (p.continuous.star.mul p.continuous).continuousOn

/-- The polynomial divided-difference remainder in the
Crouzeix--Palencia product splitting is contour integrable on every smooth
boundary. -/
theorem crouzeixProductRemainderIntegrand_contourIntegrable
    (A : E →L[ℂ] E) (Omega : SmoothJordanDomain) (p : Polynomial ℂ) :
    ContourIntegrable
      (fun z => star (Polynomial.eval z p) •
        Polynomial.aeval A (p /ₘ (Polynomial.X - Polynomial.C z)))
      Omega.boundaryParam := by
  apply ContourIntegrable.of_continuousOn
  · exact Omega.boundaryParam_contDiff.continuous.continuousOn
  · exact (Omega.boundaryParam_contDiff.continuous_deriv (by norm_num)).continuousOn
  · exact (p.continuous.star.smul
      (continuous_aeval_divByMonic_X_sub_C A p)).continuousOn

/-- The divided-difference remainder contour is a finite sum of scalar
contour coefficients multiplying powers of `A`. -/
theorem contourIntegral_crouzeixProductRemainder_eq_sum [CompleteSpace E]
    (A : E →L[ℂ] E) (Omega : SmoothJordanDomain) (p : Polynomial ℂ) :
    contourIntegral
        (fun z => star (Polynomial.eval z p) •
          Polynomial.aeval A (p /ₘ (Polynomial.X - Polynomial.C z)))
        Omega.boundaryParam =
      ∑ i ∈ Finset.range p.natDegree,
        contourIntegral
          (fun z => star (Polynomial.eval z p) *
            (p /ₘ (Polynomial.X - Polynomial.C z)).coeff i)
          Omega.boundaryParam • A ^ i := by
  by_cases hp : p.natDegree = 0
  · have hqzero : ∀ z : ℂ, p /ₘ (Polynomial.X - Polynomial.C z) = 0 := by
      intro z
      ext i
      rw [Polynomial.coeff_divByMonic_X_sub_C, hp]
      rw [Finset.Icc_eq_empty (by omega), Finset.sum_empty]
      simp only [coeff_zero]
    simp only [hqzero, map_zero, smul_zero, contourIntegral, intervalIntegral.integral_zero,
      hp, Finset.range_zero, Finset.sum_empty]
  · have hdegree (z : ℂ) :
        (p /ₘ (Polynomial.X - Polynomial.C z)).natDegree < p.natDegree := by
      rw [Polynomial.natDegree_divByMonic p (Polynomial.monic_X_sub_C z),
        Polynomial.natDegree_X_sub_C]
      omega
    have hfun :
        (fun z => star (Polynomial.eval z p) •
          Polynomial.aeval A (p /ₘ (Polynomial.X - Polynomial.C z))) =
        fun z => ∑ i ∈ Finset.range p.natDegree,
          (star (Polynomial.eval z p) *
            (p /ₘ (Polynomial.X - Polynomial.C z)).coeff i) • A ^ i := by
      funext z
      rw [Polynomial.aeval_eq_sum_range' (hdegree z) A]
      rw [Finset.smul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      rw [smul_smul]
    rw [hfun]
    unfold contourIntegral
    simp only [Finset.smul_sum, smul_smul]
    rw [intervalIntegral.integral_finsetSum]
    · apply Finset.sum_congr rfl
      intro i hi
      simp only [intervalIntegral.integral_smul_const, smul_eq_mul]
    · intro i hi
      have hcontinuous : Continuous (fun z : ℂ =>
          star (Polynomial.eval z p) *
            (p /ₘ (Polynomial.X - Polynomial.C z)).coeff i) :=
        p.continuous.star.mul (continuous_coeff_divByMonic_X_sub_C p i)
      have hcontour : ContourIntegrable
          (fun z => (star (Polynomial.eval z p) *
            (p /ₘ (Polynomial.X - Polynomial.C z)).coeff i) • A ^ i)
          Omega.boundaryParam := by
        apply ContourIntegrable.of_continuousOn
        · exact Omega.boundaryParam_contDiff.continuous.continuousOn
        · exact (Omega.boundaryParam_contDiff.continuous_deriv (by norm_num)).continuousOn
        · exact (hcontinuous.smul continuous_const).continuousOn
      simpa only [ContourIntegrable, smul_smul, smul_eq_mul] using hcontour

/-- The polynomial whose functional calculus is the normalized
divided-difference remainder contour. -/
noncomputable def crouzeixProductRemainderPolynomial
    (Omega : SmoothJordanDomain) (p : Polynomial ℂ) : Polynomial ℂ :=
  ∑ i ∈ Finset.range p.natDegree,
    Polynomial.monomial i
      ((2 * (Real.pi : ℂ) * Complex.I)⁻¹ *
        contourIntegral
          (fun z => star (Polynomial.eval z p) *
            (p /ₘ (Polynomial.X - Polynomial.C z)).coeff i)
          Omega.boundaryParam)

                                                                    
                                                                           
                                                                            
                          
                                                
                                                             
                                                                   
                                                      
                              
                                                                         
                                                            
                                                                                 
                                 
                              
              
                                                                                      
                                                                                               
                          
                     
                                                                   
                                    
                                                       
                               
                       
                                                
                                                           
                                   
                                                          
                                                    
                                      
                                                    
                                                           
                                             
                                                                  
                                                                                        
                                    
                                                                 
                                                           
                                             
                                                                  
                                                                                        
                                   
                                                                 
                                     
                                                                 
                                     
                 
                                                                     
                                                          
                                                 
                
                                                
               
                                                                  
                                                                 
                                       
                                                              
                
                                  
                                                            
               
                                                                 
                                  
                                                       
                                  
              
                                                        
                   
                      
          
                                                          
                                           
                                 
                            
           
                

                                                                 
                
                                               
                                                             
                                                      
                                                                     
                     
           
                                              
                                                                    
                                          
                               
                                                            
                                                                
                                                                                 
                                       
                                                                  
                              
              
        
                          
                     
                                                      
                                                                 
                               
                      
                         
                                                  
                                                             
                                     
               
                                                    
                                                                 
                               
                                       
                                                                 
              
                                       
                                       
          
                                   
                           
                                           
                      
                        
                                       
              
                  
                                        
           
        

                                                                       
                      
                                                          
                                                                             
                                                                             
               
                                                                               
                                                                   
                                 

                                                                             
                                 
                                                                 
                                                                         
                                                                            
                                                                                      
                                                                      
                                 

                                                                   
                                
                                                         
                                                                          
                                                                  
                                                                  
                                              
                                                                       

                                                                             
                                                      
                                                      
                                                          
                                                   
                                  
             
                                            
                                                
            
                                      
                                 
                       
                                                   

                                                                          
                            
                                                            
                                                             
                                     
                                                                                 
                                                      
                                                                         
             
                                                                               
                             
                                                                
            
                             
                                     
        
                                           

                                                                   
                               
                                                                 
                                                             
                                      
                                                                                  
                                                  
                                                                          
                                                                                    

                                                                        
                  
                                                       
                                                                            
                                                                              
                                           
            
                                      
                             
                                              
                           
                                                    
                                                               
                                                                     
                                                  
              
                                                    
                                                  
                                                  

                                                                   
                                                                       
                                                                            
                                                        
                                                                                         

                                                                      
                                                             
theorem normalized_crouzeixProductRemainderContour_eq_aeval
    [CompleteSpace E] (A : E →L[ℂ] E) (Omega : SmoothJordanDomain)
    (p : Polynomial ℂ) :
    (2 * (Real.pi : ℂ) * Complex.I)⁻¹ •
        contourIntegral
          (fun z => star (Polynomial.eval z p) •
            Polynomial.aeval A (p /ₘ (Polynomial.X - Polynomial.C z)))
          Omega.boundaryParam =
      Polynomial.aeval A (crouzeixProductRemainderPolynomial Omega p) := by
  rw [contourIntegral_crouzeixProductRemainder_eq_sum]
  unfold crouzeixProductRemainderPolynomial
  rw [map_sum]
  simp only [Finset.smul_sum, Polynomial.aeval_monomial,
    Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul, smul_smul]

/-- The product `p(A) G` is the normalized scalar-square resolvent contour
minus the normalized polynomial divided-difference remainder contour. -/
theorem aeval_mul_crouzeixPolynomialAuxiliaryOperator_eq_main_sub_remainder
    [CompleteSpace E] (A : E →L[ℂ] E) (Omega : SmoothJordanDomain)
    (p : Polynomial ℂ)
    (hOmega : closure (numericalRange A) ⊆ Omega.carrier) :
    Polynomial.aeval A p * crouzeixPolynomialAuxiliaryOperator A Omega p =
      (2 * (Real.pi : ℂ) * Complex.I)⁻¹ •
          contourIntegral
            (fun z => (star (Polynomial.eval z p) * Polynomial.eval z p) •
              resolvent A z) Omega.boundaryParam -
        (2 * (Real.pi : ℂ) * Complex.I)⁻¹ •
          contourIntegral
            (fun z => star (Polynomial.eval z p) •
              Polynomial.aeval A (p /ₘ (Polynomial.X - Polynomial.C z)))
            Omega.boundaryParam := by
  rw [aeval_mul_crouzeixPolynomialAuxiliaryOperator_eq_split A Omega p hOmega]
  rw [contourIntegral_sub
    (crouzeixProductMainIntegrand_contourIntegrable A Omega p hOmega)
    (crouzeixProductRemainderIntegrand_contourIntegrable A Omega p)]
  rw [smul_sub]

/-- The product `p(A) G` is the scalar-square resolvent contour minus
functional calculus of the explicitly constructed lower-degree remainder
polynomial. -/
theorem
    aeval_mul_crouzeixPolynomialAuxiliaryOperator_eq_main_sub_aeval_remainderPolynomial
    [CompleteSpace E] (A : E →L[ℂ] E) (Omega : SmoothJordanDomain)
    (p : Polynomial ℂ)
    (hOmega : closure (numericalRange A) ⊆ Omega.carrier) :
    Polynomial.aeval A p * crouzeixPolynomialAuxiliaryOperator A Omega p =
      (2 * (Real.pi : ℂ) * Complex.I)⁻¹ •
          contourIntegral
            (fun z => (star (Polynomial.eval z p) * Polynomial.eval z p) •
              resolvent A z) Omega.boundaryParam -
        Polynomial.aeval A (crouzeixProductRemainderPolynomial Omega p) := by
  rw [aeval_mul_crouzeixPolynomialAuxiliaryOperator_eq_main_sub_remainder
    A Omega p hOmega]
  rw [normalized_crouzeixProductRemainderContour_eq_aeval]

/-- The induction-ready product decomposition: `p(A) G` is the auxiliary
operator associated to the scalar boundary datum `|p|²`, minus functional
calculus of a strictly lower-degree polynomial. -/
theorem
    aeval_mul_crouzeixPolynomialAuxiliaryOperator_eq_squareAux_sub_aeval_remainderPolynomial
    [CompleteSpace E] (A : E →L[ℂ] E) (Omega : SmoothJordanDomain)
    (p : Polynomial ℂ)
    (hOmega : closure (numericalRange A) ⊆ Omega.carrier) :
    Polynomial.aeval A p * crouzeixPolynomialAuxiliaryOperator A Omega p =
      crouzeixAuxiliaryOperator A Omega
          (fun z => star (Polynomial.eval z p) * Polynomial.eval z p) -
        Polynomial.aeval A (crouzeixProductRemainderPolynomial Omega p) := by
  rw [
    aeval_mul_crouzeixPolynomialAuxiliaryOperator_eq_main_sub_aeval_remainderPolynomial
      A Omega p hOmega]
  rfl

                                                                           
                                                                          
        
       
                                                                                 
                                                                  
                      
                                                           
                                                                            
                                        
                                                                      
                                                                             
      
                                                                                            
                       
                       

                                                                      
                                                                          
                                           
                                                                                
                                                                  
                      
                                                           
                                                                            
                                          
                       
                                                                        
                                                 
                                          
                       
                                                
                                                                      
                                    
                                                                         
                     
                       
