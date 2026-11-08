import GraphMatrices.BoundaryCreation

/-! The side-creation bound in the actual Euclidean matrix norm. -/

namespace GraphMatrices.BoundaryCreation

set_option maxHeartbeats 1000000

noncomputable section
attribute [local instance] Classical.propDecidable

open scoped BigOperators
open OccupationCreation
open OccupationCreation.Colored

variable {C D : Type*} [Fintype C] [DecidableEq C] [Fintype D] [DecidableEq D]

def pairEnabled (incident : D → Finset C) (S U : Finset C) {n : ℕ}
    (φ ψ : C → Fin n) (source : Index incident S n) : Prop :=
  boundaryLabels S φ = source.1 ∧ boundaryLabels U φ = boundaryLabels U ψ ∧
    Disjoint (edges incident φ) source.2 ∧
    edges incident ψ ⊆ source.2 ∪ edges incident φ

                                                                               
                                                     
                                                                                         
                                                                
           
                                             
                                                                               
                                                   
                                                                                            
                       
                    
                        
                                         
                                    
                  
                                                               

private theorem card_subtype_eq_sum_indicator {α : Type*} [Fintype α]
    (P : α → Prop) [DecidablePred P] :
    (Fintype.card {x // P x} : ℝ) = ∑ x : α, if P x then 1 else 0 := by
  simp [Fintype.card_subtype]

theorem active_card_eq_sum (incident : D → Finset C) (S U : Finset C) {n : ℕ}
    (source : Index incident S n) :
    (Fintype.card (ActivePairs incident S U source.1 source.2) : ℝ) =
      ∑ φ : C → Fin n, ∑ ψ : C → Fin n,
        if φ ≠ ψ ∧ pairEnabled incident S U φ ψ source then 1 else 0 := by
  rw [card_subtype_eq_sum_indicator]
  simp only [Fintype.sum_prod_type, pairEnabled]
  apply Finset.sum_congr rfl
  intro φ _
  apply Finset.sum_congr rfl
  intro ψ _
  by_cases h : φ ≠ ψ ∧ pairEnabled incident S U φ ψ source
  · simp only [pairEnabled] at h
    simp only [h, if_true]
  · simp only [pairEnabled] at h
    simp only [h, if_false]

                                                                           
                                     
                                                                                     
                                   
                                                                                               
                                           
                                                                       
           
                                
                              
      
                                                   
                                                                                     
                             
                    
                                                 
                                                                    
                                         
                                                                  
                          
                                
               
                          
                                    
                                         
                                                                         
                                                                               
                             
               
                             
               
                          
               
                                                       
                                
                              
                               
                                             
                                                                       
                                        
                               
             
                                                                         
                                
               
                                                               

                                                                  
                                                                         
                                                                                       
                                                   

                                                                                      
                                                                          
                                                                                                   
                                                                                               
                                                                                                     

private theorem sum_subtype_le {α : Type*} [Fintype α] (p : α → Prop)
    [DecidablePred p] (f : α → ℝ) (hf : ∀ x, 0 ≤ f x) :
    (∑ x : {x // p x}, f x.val) ≤ ∑ x, f x := by
  calc
    _ ≤ (∑ x : {x // p x}, f x.val) + ∑ x : {x // ¬p x}, f x.val :=
      le_add_of_nonneg_right (Finset.sum_nonneg fun x _ => hf x)
    _ = _ := Fintype.sum_subtype_add_sum_subtype p f

                                                                                              
                                                                   
                                                              
                                                        
                                           
                                                                               
                                     
                                                                        
                                                                             
                                                                                                     
                           

private theorem spectralNorm_gram {m n : Type*} [Fintype m] [Fintype n]
    [DecidableEq m] [DecidableEq n] (A : Matrix m n ℝ) :
    spectralNorm (A.transpose * A) = spectralNorm A ^ 2 := by
  open scoped Matrix.Norms.L2Operator in
    simpa only [spectralNorm_eq_l2Operator, Matrix.conjTranspose_eq_transpose_of_trivial, pow_two] using
      Matrix.l2_opNorm_conjTranspose_mul_self A

                                                                            
                                                                     
                                                                               
                                                                                   
                                                                      
                                                      
                                                        
                                      
                                                                       
                                                       
           
                                               
                                                                   
                                             
                                          
                                      
                                                                              
                
                                                                           
                                                                                   
                               
                                                             
                               
           
                                                                
                                                     
                                                                           
             
                                                                              
                                                                              
                
                                                                   
                                                                  
        
                                                           
                                  
                      
                                                                     
                           
                                                                       
                                                         
              

                                                                            
                                                                              
                                                                    
                                                                              
                                                                 
                                      
                                                                       
                                                    
                                                            
                                                             

                                                                         
                                                                    
                                                                            
                                                 
                                                                  
                                                              
                                      
                                                                         
                                                                  
                                                                            
                                                                
                                     
                                                                                             
                                                                   
                                                       
                                                  
                                            
                             
                                                                             
                                  
                                                                   
                                 
         

end
end GraphMatrices.BoundaryCreation
