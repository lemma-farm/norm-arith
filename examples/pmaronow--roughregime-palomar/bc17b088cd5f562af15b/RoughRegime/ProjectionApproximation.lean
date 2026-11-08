module

public import RoughRegime.ProjectionPolynomial
public import RoughRegime.CombinedAnalytic
public import RoughRegime.ProjectionFrame


@[expose] public section
/-! Concrete source Gram-residual polynomial approximants. -/
noncomputable section
open scoped BigOperators Matrix.Norms.L2Operator
open Matrix MvPolynomial RealInnerProductSpace
namespace RoughRegime.ProjectionApproximation
open RoughRegime.ProjectionPolynomial RoughRegime.CombinedPolynomial
open RoughRegime.CombinedAnalytic RoughRegime.ProjectionGram
open RoughRegime.HilbertGram RoughRegime.ProjectionFrame

                                                           
                                    
                                                                   
         
                                         

                                                           
                                                                                    
                                                    
                                                               
                                           
                                                           
                        

                                                               
                                                                                    
                                                        
                                                              
                                              
                                                                                   
                                              
                                                                      
                                                                 
                                                                  
                                                                     
                                
                                                       
                                                                
                                  
                                                                                          

                                                                     
                                                                                  
                                    
                                                                       
                                                                 
                                                  
          
                                                                            
     

def polynomialEntryValuation {σ : Type*} {N n : ℕ} {dims : Fin N → ℕ}
    (Ω : Matrix (Fin n) (Fin n) (MvPolynomial σ ℝ))
    (M : (i : Fin N) → Matrix (Fin (dims i)) (Fin (dims i)) (MvPolynomial σ ℝ)) :
    Variables n dims → MvPolynomial σ ℝ
  | Sum.inl ab => Ω ab.1 ab.2
  | Sum.inr ⟨i, ab⟩ => M i ab.1 ab.2

def truncationPolynomialMatrix {σ : Type*} {N n : ℕ} {dims : Fin N → ℕ}
    (lo hi : ℝ) (Ω : Matrix (Fin n) (Fin n) (MvPolynomial σ ℝ))
    (M : (i : Fin N) → Matrix (Fin (dims i)) (Fin (dims i)) (MvPolynomial σ ℝ)) (m : ℕ) :
    Matrix (Fin n) (Fin n) (MvPolynomial σ ℝ) := fun a b =>
  MvPolynomial.eval₂Hom MvPolynomial.C (polynomialEntryValuation Ω M)
    (truncationEntryPolynomial n dims lo hi a b m)

                                                                               
                                                              
                                                                                  
                                                               
                                                                               
                                         
                                                       
                                                                             
           
                                                 
                                                         
         
              
                                
                                             

                                                                      
                                                                                
                                                                           
                                                                                         
                                                                        
                                                          
                                                          
         
                                                                        
                              
                                                                          
         
        
         
                                                                                      
         
          
                 

def bilinearPolynomial {σ : Type*} {n : ℕ}
    (u : Fin n → MvPolynomial σ ℝ)
    (S : Matrix (Fin n) (Fin n) (MvPolynomial σ ℝ))
    (v : Fin n → MvPolynomial σ ℝ) : MvPolynomial σ ℝ := u ⬝ᵥ S.mulVec v

                                                   
                                                                                  
                                              
                                                                           
                                       
                                                            
                           
                 
                                             
           
                                                
                                                    
                                  
                                               
             
                                                                                   
                                                                      

                                                             
                                                                                  
                                    
                                                    
                                             
                                                                                       
                                                 
         
          
                                              

end RoughRegime.ProjectionApproximation
