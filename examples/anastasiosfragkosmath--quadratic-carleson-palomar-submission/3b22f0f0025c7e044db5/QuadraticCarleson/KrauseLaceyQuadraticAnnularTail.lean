import QuadraticCarleson.HardyLittlewoodMaximal
import QuadraticCarleson.HilbertL2Fourier
import QuadraticCarleson.QuadraticFixedHeightAveragingNorm
import Mathlib
/-!
# Maximal tails of separated quadratic frequency pieces

This file isolates the frequency-projection part of the direct quadratic
one-node argument.  A finite tail is written as the total sum minus a
prefix.  If every prefix is a smooth low-pass projection of the total sum,
and the low-pass kernels are pointwise dominated by a fixed multiple of the
centered Hardy--Littlewood maximal function, then the whole family of tails
has a cardinality-free `L²` bound.

The application-specific input may be supplied either pointwise through
`HasLowPassPrefixControl` or almost everywhere through
`HasAELowPassPrefixControl`.  The latter is the natural interface for `L²`
Fourier multipliers.  No maximal-tail theorem or orthogonality principle is
assumed here.
-/

open Function MeasureTheory Set FourierTransform Metric
open scoped ENNReal NNReal ComplexConjugate

namespace QuadraticCarleson.KrauseLaceyQuadraticAnnularTail

set_option autoImplicit false

noncomputable section

/-- The pointwise total of a finite sequence of frequency pieces. -/
def finitePieceTotal (N : ℕ) (u : ℕ → ℝ → ℂ) (x : ℝ) : ℂ :=
  ∑ j ∈ Finset.range N, u j x

/-- The prefix strictly below `n`. -/
def finitePiecePrefix (u : ℕ → ℝ → ℂ) (n : ℕ) (x : ℝ) : ℂ :=
  ∑ j ∈ Finset.range n, u j x

/-- The finite tail beginning at `n`, represented as total minus prefix.
For `n ≤ N` this is exactly `∑_{n ≤ j < N} u_j`. -/
def finitePieceTail (N : ℕ) (u : ℕ → ℝ → ℂ) (n : ℕ) (x : ℝ) : ℂ :=
  finitePieceTotal N u x - finitePiecePrefix u n x

                                  
                                                    
                                                               
                                                                
                                                           
               
      

                                                         
def finitePieceTailMax (N : ℕ) (u : ℕ → ℝ → ℂ) (x : ℝ) : ℝ≥0∞ :=
  (Finset.range (N + 1)).sup fun n ↦ ‖finitePieceTail N u n x‖ₑ

                                                                      
                                                                    
                             
                                                                        
               
                                
                                        
                                             

                                                                         
                                                                           
                                                                                
def HasAELowPassPrefixControl (N : ℕ) (u : ℕ → ℝ → ℂ) (A : ℝ≥0∞) : Prop :=
  ∀ n ≤ N, ∀ᵐ x : ℝ ∂volume,
    ‖finitePiecePrefix u n x‖ₑ ≤
      A * centeredHardyLittlewoodMaximal
        (fun y ↦ ‖finitePieceTotal N u y‖ₑ) x

                                  
                                      
                                         
                                         
            
                            

                                                                           
                                                                       
                                                                        
                                                                         
                               
                                                        
                                                   
                       
                                                                 
                                                             
             
                             
                                                                 
                
                                        
                       
                                                            
                             
                                                                    
                                             
                       
                          
                                                                     
                                    
                                         
                                                                     
                                 
                                      
                     
                                
                
                                                                                  
                  
      
                                                         
                                         
                                        
                                                             
                                                      
                                                       
                                         
                                        
                                                      
                                 
                                                   
                                
            
                                                                   
                              
                                                
                                                      

                                                                         
                                                                          
                                      
                                                        
                                      
                                
                                              
                            
                               
                                                  
                         
                                                            
                           
                                                      
                                       
              
                     
                                                       
             
                           
                                                
                                                              
          
                                    

                                               
                                      
                                                       
                              
                                 
                                          
                                                     
                     
            
                        
                                                                                   
                          
                                         

/-- Almost-everywhere tail domination from almost-everywhere prefix control.
The exceptional sets for the finitely many prefixes are intersected before
taking the finite supremum. -/
theorem finitePieceTailMax_le_total_add_maximal_ae
    {N : ℕ} {u : ℕ → ℝ → ℂ} {A : ℝ≥0∞}
    (hprefix : HasAELowPassPrefixControl N u A) :
    ∀ᵐ x : ℝ ∂volume,
      finitePieceTailMax N u x ≤
        ‖finitePieceTotal N u x‖ₑ +
          A * centeredHardyLittlewoodMaximal
            (fun y ↦ ‖finitePieceTotal N u y‖ₑ) x := by
  have hall : ∀ᵐ x : ℝ ∂volume,
      ∀ n ∈ Finset.range (N + 1),
        ‖finitePiecePrefix u n x‖ₑ ≤
          A * centeredHardyLittlewoodMaximal
            (fun y ↦ ‖finitePieceTotal N u y‖ₑ) x := by
    rw [Filter.eventually_all_finset]
    intro n hn
    exact hprefix n (Nat.lt_succ_iff.mp (Finset.mem_range.mp hn))
  filter_upwards [hall] with x hx
  apply Finset.sup_le
  intro n hn
  exact enorm_sub_le.trans (add_le_add le_rfl (hx n hn))

                                                           
                                      
                                           
           
                         
                                                                        

                                                    
                                          
                                            
           
                          
                                              

                                                          
                                          
                                         
                                                  
                                       

                                                             
                                  
                                             
           
                           
                                                               
                 
                        
                                   
                                                          

                                           
                                                                            
                                                               
                                           
                                                      
                                                                
             
                           
                                                                         
                                                           
                                                                          
             
                            
                                                                         
                                                           
                                                                        
                          
                                
           
                           
                                                               
                 
                        
                                   
                                  

                                                            
                                           
                                      
        
                                  
                                                       
                                
                                                 
                      
                         
                              
                                       
                               
      
                                                             
                                    
                                                      

                                                                          
                                                                                       
                                   
                                          
                                      
                                
                                               
                                          
                         
                                                 
                                                       
                                                      
                           
                                                      
                       
                                    
                                           
                                                                                        
                                                     
      
                                          
                                              
                           
                                                           
                       
                                                 
                                            
                                       
                                                                                  
                                                                  
            
                                                             
                                                    

                                                                      
                                                                     
                                                                              
                                             
                                      
                                
                                                 
                                          
                         
                                                 
                                                       
                                                      
                           
                                                      
                                 
                                    
                                           
                                                                                 
                                       
                                                     
      
                                          
                                              
                              
                                                           
                       
                                                 
                                            
                                       
                                                                                  
                                                                  
            
                                                             
                                                    

                                                                  
                                                                           
                     
                                      
                                                          
                
                     
                                                   
                                                 

                                                                
                                                         
                                                                          
                           
                                       

                                                                    
                                                                       
                                                     
                                                              
                                                                
                                                 
                                                       
                                              
               
                                                      
                       
                                                                               
                                 
                               

                                                
                                                
                                                 
                             
                                 
                            
                   
                                             

                                                                          
                                                                          
                 
                                                             
                              
                                    
                                                   
                                                 
           
                                            
                 
                        
                                                          
                      
                                           
                                                       
                                                
          
                                                                    
                                   
                                                
                                    
                                                               
                                                  
                                                                

                                     
                                              
                                      
                                                               
                                      
           
                                            
                                    
                        
                                        
                                             
                                                      

                                                      
                                      
                                               
                                                             
                                                       

                                                            
                                      
                                                             
                                                   
                                                                    
            
                                                  
                                                          
                                                    
                                                          
                                                  
                                               

                                                                           
                                                     
                                          
                           
                                    
                                              
                                    
                                                 
                                                            
                                                                 
              
                                                                     
                                             
                                        
                                                               
                             
      
                                                 
                                                                            
                        
                      
                                                                             
                                                          
                                                                         
                                                              
                                       
                                 
                                                              
                                
               
                                                                         

                                            
                           
                                    
                                              
                                    
                                           
                                                    
                                 
                                      
                                                  

                                                                           
                                                                         
                                                                            
                           
                                              
                                      
                                   
                                    
                                              
                                  
                                               
                                          
                         
                                                      
      
                           
                                              
                                                      
                                                                 

                                                                        
                                                                   
                                                 
                                      
                                   
                                    
                                              
                                  
                                                 
                                          
                         
                                                      
      
                           
                                              
                                                         
                                                                 


end
end QuadraticCarleson.KrauseLaceyQuadraticAnnularTail
