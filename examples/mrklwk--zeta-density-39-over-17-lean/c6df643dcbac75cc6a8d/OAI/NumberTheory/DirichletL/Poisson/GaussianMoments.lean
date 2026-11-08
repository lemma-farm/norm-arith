module
public import OAI.NumberTheory.DirichletL.GaussSum.GaussianFiberMass
public import Mathlib
@[expose] public section

namespace OAI

noncomputable section

open scoped BigOperators
open MulChar AddChar
open scoped BigOperators
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped FourierTransform SchwartzMap
open Finset Complex
open scoped Classical
open scoped Classical
open Filter Real Asymptotics

namespace GaussianMoment

                                            
                                                     
                                            
                                         
            
                                                                     
      
                                                                
                                                    
            
                                     
                         
             
             

                                                                        
                           
                                             
                                                      
                            
      
                           
                                                 
                    
                                            
                                       
                                                    

end GaussianMoment
namespace ActualEisensteinCubic

section

open ShortDraftLatticeCount

                                             
                                                        
                               
                                                 
                                                          
           
                             
                                                 
                                          
                                               
                                
                     
                                                                      
                                                               
           
                                                               
                                           
                                           
                                 
              
                                                  
                                             
                                                                       
                                                                        
                                               
                                    
                                                        
                                                                   
                                               
                                    
                                                        
                                                                   
                         
                                                         
        
                                                           
                                                         
                                                          
                              
      
                                
                     
                                                                      
                                
                                                                          
                                
                             
                
                                                 
                                 
                                                                 
                          

theorem rational_qNat (r : ℕ) (hr : r ≠ 0) :
    qNat (r : O) = r ^ 2 := by
  calc
    qNat (r : O) = Ideal.absNorm (Ideal.span {(r : O)}) :=
      qNat_eq_absNorm_span _
    _ = Nat.card (O ⧸ Ideal.span {(r : O)}) := by
      rw [Ideal.absNorm_apply, Submodule.cardQuot_apply]
    _ = r ^ 2 := rational_modulus_card r hr

                                                  
                                          
                  
           
                                             
                
          
                                  
                                                   
                                 
                                                                   
                                                          

                                  
                                                       
               
                                                          
                                       
                                                                             

                                    
                                                          
                                 
                                       
                                       
                                             
           
                                                              

theorem rational_qNat_eq_one_iff (x : O) : qNat x = 1 ↔ IsUnit x := by
  rw [qNat_eq_absNorm_span, Ideal.absNorm_eq_one_iff,
    Ideal.span_singleton_eq_top]

theorem rational_prime_factor_cases (r : ℕ) (hr : r.Prime) :
    (Ideal.span {(r : O)} : Ideal O).IsMaximal ∨
    ∃ a b : O, a ≠ 0 ∧ b ≠ 0 ∧ (r : O) = a * b ∧
      qNat a = r ∧ qNat b = r ∧
      (Ideal.span {a} : Ideal O).IsMaximal ∧
      (Ideal.span {b} : Ideal O).IsMaximal := by
  have hru : ¬ IsUnit (r : O) := by
    rw [← rational_qNat_eq_one_iff, rational_qNat r hr.ne_zero]
    have htwo := hr.two_le
    nlinarith
  rcases irreducible_or_factor hru with hirr | ⟨a, b, hna, hnb, hab⟩
  · left
    exact PrincipalIdealRing.isMaximal_of_irreducible hirr
  · right
    have hqa1 : qNat a ≠ 1 := by
      intro h
      exact hna ((rational_qNat_eq_one_iff a).mp h)
    have hqb1 : qNat b ≠ 1 := by
      intro h
      exact hnb ((rational_qNat_eq_one_iff b).mp h)
    have hqprod : qNat a * qNat b = r ^ 2 := by
      rw [← qNat_mul, ← hab, rational_qNat r hr.ne_zero]
    obtain ⟨hqa, hqb⟩ := (hr.mul_eq_prime_sq_iff hqa1 hqb1).mp hqprod
    have ha0 : a ≠ 0 := by
      intro h
      have hqa0 : qNat a = 0 := by simp [h, qNat_eq_absNorm_span]
      rw [hqa] at hqa0
      exact hr.ne_zero hqa0
    have hb0 : b ≠ 0 := by
      intro h
      have hqb0 : qNat b = 0 := by simp [h, qNat_eq_absNorm_span]
      rw [hqb] at hqb0
      exact hr.ne_zero hqb0
    have hpa : Prime a := by
      apply Ideal.prime_of_irreducible_absNorm_span ha0
      rw [← qNat_eq_absNorm_span, hqa]
      exact hr.prime.irreducible
    have hpb : Prime b := by
      apply Ideal.prime_of_irreducible_absNorm_span hb0
      rw [← qNat_eq_absNorm_span, hqb]
      exact hr.prime.irreducible
    exact ⟨a, b, ha0, hb0, hab, hqa, hqb,
      PrincipalIdealRing.isMaximal_of_irreducible hpa.irreducible,
      PrincipalIdealRing.isMaximal_of_irreducible hpb.irreducible⟩

                                    
                                            
                                                                 
                            
                                              
                                                 
                                        

                                                           
                              
                               
                                                  
                                                     
                                                     
                                               
                                                          
                                                                
                                                     
                                                   
                         
                         
                    
                                                                       
                                       
              
              
                    
                     
                                                     
                                                                  
                                                                  

end

                                       
                                                        
                               
                                                 
                                                   
                                                        
                                                                 
                                               
                                
                     
                                                                            
                                   
                                              
                                   
                               
                                                            
                           
                                                          
                                                      
                  
                                
                                                     
                                                      
                  
                                
                                                     
                                                    
                                                        
                            
                                                           
                                  
                                                           
                                  
             
                                                    
                                                    
                                   
                                           

end ActualEisensteinCubic

open ActualEisensteinCubic

namespace RationalPrimeExtraction

noncomputable def selected (Y : ℝ) : Finset ℕ :=
  (Finset.Ioc ⌊Y / 3⌋₊ ⌊Y⌋₊).filter Nat.Prime

                               
                                                                          
                               
                                                            
                                                       
                                   
                                                        
                                                         
                                                            
                 
                                
                                                     
                                            
                                                  
                                             
                     
                                      
                                                                   
                                                                  
                                              
                                                               

end RationalPrimeExtraction

namespace OscSpecial

                                                
                                                         
               
                                                   
                                                 
                                        
            
                                                         
                                           
                                                          
                                                    
                               
                                                 
                                                             
            
                                                          
                                              
                                                              
                                         

                                                         
                                                   
                                                  
                             
             
                 

                                                               
                                      
                                                         
                                                         
             
                                      
                                                                      
                                                    
                                  
          
                
            
                                      
                                                                      
                                                
                                  
          
                
            

                                                           
                                                   
                                        
                                                                   
                            
                                                          
             
                          
             
                                      
                         
                       
                                         
        

                                                          
                                                   
                                                               
                                                            
                                                       
                                                                   
                                                     
            
                                                      
                                                        
                                                                         
             
        
                                    
                                          
                                                                   
                  
                 

                                                                   
                       
                                                     
                                              

                                                         
                             
                                
                                                          
                                                           
                                                                            

                                                        
                                          
                                                             
                                                      
                        
         
                       
      

                                                          
                                
                                    
                                        
                                                       
                        
           
                  
                                                              
                                      
                                          
                                                             
                                  
                                               
                                   
                   
                                        
                        
                                          
                                                   
                                                 
                           
                                             
                                   
                                                          
                                                           
                                                             
                                                                                  

                                                                     
                                                                       

                                                           
                               
                                                               
                                
                                                              

                                                     
                                                        
                                                        
                          
               
                                        
                                                      
                              
                                                         
                                                    
                           
                                             
                                     
                          
               
                                                                        
                                          
                                                             
                                                             

                                                                    
                                                      
                                

                                                                               
                                
                                                                
                                       
                                                                    
                                                  
                 

                                                    
                             
                                                  
                                         
                                                                
                                    
                        
         
                                    
                     
                                                                   
             
                               

                                                         
                                
                                    
                                        
                                                      
                          
               
                                        
                                                      
                              
                                                               
                                                                                  
                           
                                             
                                      
                                      
                                                                          
                                                    
                                                          
                                                                                 
                                                
                                                             
                                            
                                                                  

                                                            
                                
                                    
                                        
                                                           
                                     
                                                               
                                                
                                                              
                                                     
                                       
                                                           
                                             
                                                  
                                                 
      
                                                           
                             
                                                          
                                                            
                                                           
                                       
                                                                 
                                         
                                           

noncomputable def q (a b : ℝ) : ℝ := a ^ 2 - a * b + b ^ 2
noncomputable def A (η a b : ℝ) : ℂ :=
  (η : ℂ) + 2 * Complex.I * (b : ℂ) / (q a b : ℂ)
noncomputable def B (η a b : ℝ) : ℂ :=
  -(η : ℂ) / 2 - 2 * Complex.I * (a : ℂ) / (q a b : ℂ)
noncomputable def D (η a b : ℝ) : ℂ :=
  (η : ℂ) + 2 * Complex.I * ((a-b : ℝ) : ℂ) / (q a b : ℂ)
noncomputable def R (η a b : ℝ) : ℝ := 4 / q a b + 3 * η ^ 2 / 4

                                                      
                                                                     
                                                      

                                                              
                                                           
                                                    
                                                                                 
            
                                                                           
            
             
                 
                  
             
         
                     
      

                                                                          
                                                            
                                                
                 
                              

end OscSpecial

end

end OAI
