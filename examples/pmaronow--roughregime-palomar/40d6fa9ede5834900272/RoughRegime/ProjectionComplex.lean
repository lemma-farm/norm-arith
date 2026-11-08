module

public import RoughRegime.ComplexPolynomialKernel
public import RoughRegime.UniformExpressionFamily
public import RoughRegime.ProjectionIncrementPolynomial
public import RoughRegime.ComplexDerivativeBridge
public import Mathlib

@[expose] public section
/-! Uniform complex bounds for the actual substituted projection polynomials. -/
noncomputable section
open scoped BigOperators Matrix.Norms.L2Operator
open Matrix MvPolynomial
namespace RoughRegime.ProjectionComplex
open RoughRegime.KernelExpressions RoughRegime.ComplexPolynomialKernel
open RoughRegime.CombinedPolynomial RoughRegime.ProjectionApproximation
open RoughRegime.Upper RoughRegime.ComplexDerivativeBridge

 def complexEvaluation {σ : Type*} (t : σ → ℂ) : MvPolynomial σ ℝ →+* ℂ :=
  MvPolynomial.eval₂Hom Complex.ofRealHom t

lemma complexEvaluation_eq {p : ℕ} (t : Fin p → ℂ) (P : MvPolynomial (Fin p) ℝ) :
    complexEvaluation t P = MvPolynomial.eval t (complexify P) := by
  rw [complexify, MvPolynomial.eval_map]
  rfl

                                                                         
                                                                 
                                                                        

                                                                            
             
                    

                                               
                                                         
                                                                                       
                                        
                                                                                  
                                          
                                                

                                                                              
                                             
                                                                                    
                                 
                                                                      

                                                                       
                                                         
                                                                                     
                                   
                                                                        
                                                                                       
                                                                     
                                                                                      
                                                               
                                                                   
                  

                                                                                  
                                                                            
                                                                     
                                                                                     
                                           
                                                                      
                                                     
                                                                                  
                             
                                                       
                                   
                                
                                                                           
                                                             
         
                                                                             
                                                         
                                                        
            
                   
         
                                                                   

                                                                              
                                                                         
                                                                         
                                              
                                                      
                                                         
                                                                                     
                                                               
                                                                                
                                      
                                              
                                                                                                 
                                                      
           
                                                                                                      
                                                                         
                                                        
                                                                      
                                
                  
                                                                      
                        

end RoughRegime.ProjectionComplex
