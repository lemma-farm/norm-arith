module

public import NearlyMinimax.PaperIncrement
public import RoughRegime.ComplexDerivativeBridge


@[expose] public section

/-! Degree-independent complex-neighborhood bounds for the actual reciprocal polynomials. -/

noncomputable section
namespace NearlyMinimax
open scoped BigOperators
open Polynomial

section ChebyshevPerturbation
variable {R : Type*} [Ring R] [Algebra ℝ R]

                                                                           
                                                                     

                                                     
                                                                                                
                         
                                                                         
                  

                                                     
                                                                                                
                         
                          
                  

                                                                                        
                                             
                                                             

                                                        
                                                                  

                                                                  
                                   
                                                                                       
                          
           
                                                                          
           
                                                  
                                               
                                         
                                                                 
                                                  
                                                                                 
                             
                                                                                            
                                                                                  
                                                                                  
                                               
                                                                             
                   
                                                                          
              

                                                                                               
                                                                  
                                                 
                                                        
                                             
                                                      
                                                                                         
                    
                                                                 
                                                
                                                                     
                

end ChebyshevPerturbation

                                                                                             
                                                                           

                                                                     
                                    
                                                                   
                                                                               
                             
                                              
      

                                                                                     
                                                                                          
                                                                   
                                                                               
                                 
                                                                           
                                  
         
      
                                                                   
                                
                
                  
                                                             
                             
                
                   
          
                                                      
                                              
                                                          
                        
                                                                        

                                                                         
                                                             
                                           
                                                 
                                
                                                              
                         
                                                
             
                                                  
                                           
                                                     
                                        
                                                 
                                                             
          
                                                                                 
                                                    
                                                              
                        
                                        
                                                     
        
                                                                                          
                                                             
                                               
                                                                             
                                           
                                                  
                                                                        
                                                                                 
                             
            
                                               
                                                         
                                                                                             
                          

section ChebyshevNorm
variable {R : Type*} [NormedRing R] [NormedAlgebra ℝ R] [NormOneClass R]

                                                   
                                                                                   
                                                     

                                                                                         
                                                    
                                             
                                   
          
                                                                
                                                                                            
        
                                            
                                              
                          
                    
                                                    
                                                                         
                                              
                                                                                        
                      
           
        
                                                                                            
                                                                
                                                                                       
                                                           

                                                               
                                
                                                                   
                         
                   
           
                                                                        
        
                                                                         
                                                
                                                          
                                                                     

                                                
                                                               
                                
                                        
                                                                            
                                                
                                                                       
                                                                  
                                      
                                                                 
                                                                 
                                                          
           
        
                                                      
                                                     
                                       
                                             
                                                                                             
                                         
                               
                                                         
                                                        
                                                          
                                 
         
      
                                                                                                  
                                 
                                                                          
                                         
                                 
                                                               
                                                      
                                   

                                                                                   
                                                                               
                                                     
                                                    
                                           
                                                                              
                                         
                                                                                        
                                                     

end ChebyshevNorm

section PowerSeriesBounds
variable {R I : Type*} [NormedCommRing R] [NormOneClass R] [DecidableEq I]

/-- Finite Cauchy products preserve a common geometric envelope in any normed
commutative ring, including the complexified matrix entries. -/
theorem powerSeries_prod_geometric_bound (s : Finset I) (f : I → PowerSeries R)
    (q B : ℝ) (hq : 0 < q) (hB : 0 ≤ B)
    (hf : ∀ i ∈ s, ∀ k, ‖PowerSeries.coeff k (f i)‖ ≤ B * q ^ k) (k : ℕ) :
    ‖PowerSeries.coeff k (∏ i ∈ s, f i)‖ ≤
      B ^ s.card * ((k + 1 : ℕ) : ℝ) ^ s.card * q ^ k := by
  induction s using Finset.induction_on generalizing k with
  | empty =>
    simp only [Finset.prod_empty, Finset.card_empty, pow_zero, one_mul, PowerSeries.coeff_one]
    split_ifs with hk
    · subst k; simp
    · simp only [norm_zero]; positivity
  | @insert a s ha ih =>
    rw [Finset.prod_insert ha, mul_comm]
    have hh := RoughRegime.SeriesBounds.convolution_coefficient_bound
      (fun j => PowerSeries.coeff j (∏ i ∈ s, f i))
      (fun j => PowerSeries.coeff j (f a)) s.card k q (B ^ s.card) B hq
      (by positivity) hB
      (fun j => ih (fun i hi => hf i (Finset.mem_insert_of_mem hi)) j)
      (hf a (Finset.mem_insert_self ..))
    rw [PowerSeries.coeff_mul]
    simpa only [RoughRegime.SeriesBounds.convolution, Finset.card_insert_of_notMem ha,
      pow_succ] using hh

end PowerSeriesBounds

section ComplexMatrices
open scoped Matrix.Norms.L2Operator
open RoughRegime.Upper RoughRegime.MatrixUpper RoughRegime.MatrixDeterminant
variable {n : Type*} [Fintype n] [DecidableEq n] [Nonempty n]

                                                                    
                                                              

                                                                                  
                                                                                              
                                      
         
                                          

                                                                                           
                                                                                            
                                                            
                                          
                                                                         
                              
                                 
            
                                                 
                                                
                                                        

                                                              
                                                       
                                                 
                                         
         
      

                                                                                  
                                                         
                                  
                                                    
                                       
                                     
                                                                                             
                   
                                                                         
                    

                                                                                 
                                                                                      
                                                                                          

                                                                                   
                                                                                    
                                                     
                                                 
                                                                            
                                                     
                                           
                                                
                                                       
                                                                       
                             
                                    
                                                                                         
                                      
                                          
                   
           
                           
                                                                  
                                      
                                 
                               
        
                                                                                                         
                                                                                       
                      

                                                                                         
                                                                                    
                                                     
                                                 
                                                                  
                       
                                                             
                                           
                                                       
                                             
                                                                                           

theorem determinant_series_coefficient_bound (K : Matrix n n (PowerSeries ℂ))
    (q B : ℝ) (hq : 0 < q) (hB : 0 ≤ B)
    (hK : ∀ i j k, ‖PowerSeries.coeff k (K i j)‖ ≤ B * q ^ k) (k : ℕ) :
    ‖PowerSeries.coeff k K.det‖ ≤
      (Fintype.card (Equiv.Perm n) : ℝ) * B ^ Fintype.card n *
        ((k + 1 : ℕ) : ℝ) ^ Fintype.card n * q ^ k := by
  have hsign (σ : Equiv.Perm n) (P : PowerSeries ℂ) :
      ‖PowerSeries.coeff k (Equiv.Perm.sign σ • P)‖ = ‖PowerSeries.coeff k P‖ := by
    obtain hs | hs := Int.units_eq_one_or (Equiv.Perm.sign σ)
    · rw [hs]; simp
    · rw [hs]; simp [Units.smul_def]
  rw [Matrix.det_apply, map_sum]
  calc
    _ ≤ ∑ σ : Equiv.Perm n, ‖PowerSeries.coeff k (Equiv.Perm.sign σ • ∏ i, K (σ i) i)‖ :=
      norm_sum_le _ _
    _ = ∑ σ : Equiv.Perm n, ‖PowerSeries.coeff k (∏ i, K (σ i) i)‖ := by
      apply Finset.sum_congr rfl; intro σ hσ; exact hsign σ _
    _ ≤ ∑ _σ : Equiv.Perm n,
        B ^ Fintype.card n * ((k + 1 : ℕ) : ℝ) ^ Fintype.card n * q ^ k := by
      apply Finset.sum_le_sum
      intro σ hσ
      simpa using powerSeries_prod_geometric_bound Finset.univ (fun i => K (σ i) i) q B hq hB
        (fun i hi => hK _ _ ) k
    _ = _ := by simp [mul_assoc]

                                                                          
                                                                            
                                                                            
                                                     
                                                             
                                                             
                       
                                                                       
                                                                      
                                                                        
                                                                           
                                             
                                                               
                                                                
                                        
                                                                     
                                                                                 
                                                                                     
                                                                                          
                                                                                 
                                                                                                            
      
                                                                                            
                                                                                           
                                              
                                                                              
                                                                                                    
                                  

                                                                                
                                                                        
                                                      
                                   
                                                                      
                
                                                                                              
                         

                                                                                    
                                                                        
                                                           
                                    
                              
                                                                                  
                                                                           
                                            
     

                                                                          
                                                                                                         
                                                                               
           
                                                                       
                                                                             
                                                  

                                                                                
                                                                
                                    
                   
             
             
                                                                              
                        
                   
             
             
                                                                       

                                                                                                     
             
         
                                                                             

                                                                            
                                                          
                                                                         
                                                              
                                    
                                                                                          

end ComplexMatrices

section ComplexFreeCoordinates
                                   
                                                                                   
                           

                                                                                          
                             
                                  

                                                                              
                                          
                                                                    
                                                             
                                                                                    
       
                                                                          
                                         

                                                      
                                                    
                                                                                            
                                                                                                      
                                                         
                                                                             

                                                          
                                                  
                                                                                            
                                                                  
                                             
                                                             
                                                                                                          
                                        
                                                         

                                                             
                                                            
                                                                       
                                                    
                                                       
                                   
                                                                                                         
                                                                                                    
                                                                 
                                                                               
                                                                                             
                                                                
                                                                                             
                                                                                
                              
         
                            
            
                                                         
                                  
          

end ComplexFreeCoordinates

section PolynomialBounds
                                                

                                                                                                 
                                                                   
                                                 

                                                                                      
                                           
                                  
            

                                                                              
                                                
                                                                                    
                             
      
                                                                                                
               
                             
                
                              
                                                         
                            
                                                       
                                                            
                
                   
                                                     

end PolynomialBounds

section CoordinateOperators
                                   
                           

                                                                                             
                                             
                     
                      

                                                                                            
                                                  
                     
                      

                                                                                       
                                                   

                                                                                      
                                                  

                                                                                         
                                                                      

                                                                                        
                                                                          

                                                                    
                                                                                                     
          
              
                 
            
                         
                                            
           
       

                      

                                                                                      
                                                
                                         
                                          
                                                            

                                                                              
                                               
                                              
                                
                            
                               
                                                              

                                                        
                                                                
                                                       
                                                                   
                                                                     
                                                                  
                                          
                                                 
                                                         
                                                                           
                                                             
                                  
                                                                  
      
                                                           
                                                              
                          
                      
                                                        
                                                                                  
                                                                   

end CoordinateOperators

section UniformNeighborhood
                                   
                      
                           

                                               
                                               
                                                             
                                                 

                                                                                          
                                    
                                                                                

                                                                  
                                              
                               
                                  
                                            

                                                                                        
                                                       
                                                               
                                                      
                                                  
                                                 
                                                                     
                                                                    
                                                                             
                                                                                         
                                                                          
                                          
                                 
                                                      
                                                                 
                                                 
                                                                                
                                                                                     
                                                           
              
            
                                                                         
                                                                     
                                                                         
                                                                   
                                                                 
                                                                                             
                                                                 
                                                                                           
                                     
           
                                     
        
                                                       
                                                                 
                      
                       
                                             
                                                                                     
                                                                    
                                                               
                                                                             
                                    
                                                                                  
                                                                            
                                                                                      
      
                                                            
                                                                                    
                                                                                                
                                                                             
                                                                             
                             
                
                   
                             
                                                                             
                                                                       
                                          

end UniformNeighborhood

section ActualDerivatives
                                   
                                                          
                           

                                                                                            
                                                                     
                                 
                                                                 
                                                               
                                              

                                                                                            
                                         

                                                                                           
                                              

                                                                     
                                                 
                                                      
         
                               

                                                                                    
                                                       
                                                               
                                                 
                                                        
                                                       
                                                                           
                                                                          
                                      
                                                                 
                                                                                               
                                                                          
                                                                                          
                                                                               
                                                              
                                                                           
                                                         
                           
                                           
           
                                                                     
                     
                                                                                                      
                                                                                                    
                                                          
              
                                     
                                                         
              
                                     
                                                                             
                                               
                
                                                                            
                                               
                
                                                   
                                                         
            
                                                                                           
                                                                                
                                                                                      
                                                              
                                                                                   
            
                   
         
                                         

end ActualDerivatives
end NearlyMinimax
