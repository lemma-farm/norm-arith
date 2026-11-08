module

/-
Good degrees under pure laws, maps and mixtures, and independent product laws.
-/
public import GraphMarkovMatching.Potential.Directed

@[expose] public section

namespace GraphMarkovMatching

open GraphMarkovMatching.Support
open scoped ENNReal Classical

universe u
variable {X : Type u}

noncomputable def goodInd (R : X → X → Prop) (z y : X) : ℝ≥0∞ :=
  if R z y then 1 else 0

lemma rE_eq_tsum_mul (ν : PMF X) (R : X → X → Prop) (z : X) :
    rE ν R z = ∑' y, ν y * goodInd R z y := by
  rw [rE]
  exact tsum_congr fun y => by by_cases h : R z y <;> simp [goodInd, h]

                                                                              
                                                          
                                   

                                                                         
             
                                                      
                                    
                                                  

                                                                  
                                
                                                                 
                                    
                                          

                                                                
                                        
                                                
              
                                                            

                                                               
                                                      
         
                                                      
                                                                    
           
                      
                                    
                              
              
      

                                                                    
                                     
                                                         
                                           
               
         
                                           
                                                              
                                                                  
                                   
                                                        
                                                                         

                                                                                        
                                                                    
               
         
                                           
                                       
                                                                     
                                                             


                                                         
                                          
                                                                             
                                                                           
                       


lemma tsum_mass_prod (μ₀ μ₁ : PMF X) (F G : X → ℝ≥0∞) :
    ∑' p : X × X, prodPMF μ₀ μ₁ p * (F p.1 * G p.2)
      = (∑' x, μ₀ x * F x) * (∑' x, μ₁ x * G x) := by
  rw [tsum_congr fun p : X × X => show prodPMF μ₀ μ₁ p * (F p.1 * G p.2)
      = (μ₀ p.1 * F p.1) * (μ₁ p.2 * G p.2) from by rw [prodPMF_apply]; ring]
  exact tsum_prod_split (fun x => μ₀ x * F x) (fun x => μ₁ x * G x)

end GraphMarkovMatching
