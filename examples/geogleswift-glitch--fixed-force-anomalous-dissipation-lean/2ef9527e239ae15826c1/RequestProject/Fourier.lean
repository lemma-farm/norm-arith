module

public import RequestProject.Controls
public import RequestProject.DampedResponse
public import RequestProject.TorusFourier
public import RequestProject.WeightedFourier
public import RequestProject.NonStationary

/-!
# Section 3: Fourier estimates for advection–diffusion

Quasi-periodic Fourier coefficients of torus diffeomorphisms (Definition 3.2), the semiclassical
observable lemma, the non-stationary phase bound, the weighted Fourier drift estimate
(Lemma 3.5), the cell problem and its Lie splitting (Definitions 3.6–3.7, Lemmas 3.8–3.10) and
the diffusive Fourier drift estimate (Proposition 3.11).
-/

@[expose] public section

open MeasureTheory Set Filter Topology Real ProbabilityTheory
open scoped ENNReal ContDiff Matrix NNReal

noncomputable section

namespace AnomDiss

/- The coefficients `coeffC` (Definition 3.2), the weights `weightW` and the Parseval part of
**Lemma 3.3** (`coeff_parseval`) are in `RequestProject/SemiclassicalCore.lean`. -/

                                                                                      
                                                                                         
                        
                                                                                                 
                                                                     
                                                                                         
                                                                        
                                                         
                                                 
                                               
                                  
                                  

                                                                                      
                                                      
                                                                                           
                                                            
                                                                           
                                                           
                                                                              
                                                                      
                                                   
                                                                                         
                                      
                                        

                                                                                          
                                                                                                
                                                                                              
                                                                                             
                                                                 
                                                                                            
                                                                          
                                                           
                                       
                                                                       
                                                                                    
                                     
                                                               
                                                
                                   
                                                                                                  
                                                                                   
                                                                              
                                                          
                                              
                                           

                                                       

                                                                                     
                                                                                       
structure IsCellSolution (B : ℝ → Pt 2 → Pt 2) (μ : ℝ) (ξ : Pt 2) (h : ℝ → Pt 2 → ℂ) :
    Prop where
  regular : ∃ β, 0 < β ∧ β < 1 ∧ IsParabolicC12 1 β h
  quasi_periodic : ∀ s ∈ Icc (0 : ℝ) 1, ∀ y (n : Fin 2 → ℤ),
    h s (y + intVec n) = expChar ξ (intVec n) * h s y
  init : h 0 = expChar ξ
  eqn : ∀ s ∈ Icc (0 : ℝ) 1, ∀ y,
    dt 1 h s y + conv (B s) (h s) y = (μ / (4 * π ^ 2)) • lap (h s) y

                                                                                             
                                                                  
                                                    

                                                          
                                                                                  
                                            
                                                          
                                        

                                                                
def gauss2 (v : ℝ≥0) : Measure (Pt 2) := Measure.pi fun _ : Fin 2 => gaussianReal 0 v

                                                                                    
                      
                                                                                

                                                                                  
                                                                               

                                                                                                
                                                                             
             
                                                                     

                                                                                              
                                     
                                                                   
           
                                                                

                                                                                
def gaussSeq (v : ℝ≥0) : Measure (ℕ → Pt 2) := Measure.infinitePi fun _ : ℕ => gauss2 v

                                                                               
                                                                             
                                                                               

                                                                 
                                                                                                       
                                                                     

                                                                
                                  

                                            
                                
                                                                                                

                                                               
                                 

                                                                     
                                          

end AnomDiss
