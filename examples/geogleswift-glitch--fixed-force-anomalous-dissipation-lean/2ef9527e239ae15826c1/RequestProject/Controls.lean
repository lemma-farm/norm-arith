module

public import RequestProject.Shears

/-!
# Section 2.2: controls with vanishing time moments

The four-dimensional space `𝓔` of shear eigenfields, flows of controls, the moment correction
lemma, controls realizing the block maps with vanishing time moments (Lemma 2.13), the block
parameter space `Ω_b` (Definition 2.14) and the damped response `B_{μ,ω}` (Definition 2.15,
Lemma 2.16).
-/

@[expose] public section

open MeasureTheory Set Filter Topology Real
open scoped ENNReal ContDiff Matrix NNReal

noncomputable section

namespace AnomDiss

/-- The basis `(sin 2πy, 0), (cos 2πy, 0), (0, sin 2πx), (0, cos 2πx)` of `𝓔`. -/
def eBasis (i : Fin 4) (x : Pt 2) : Pt 2 :=
  match i with
  | 0 => ![Real.sin (2 * π * x 1), 0]
  | 1 => ![Real.cos (2 * π * x 1), 0]
  | 2 => ![0, Real.sin (2 * π * x 0)]
  | 3 => ![0, Real.cos (2 * π * x 0)]

/-- The element `∑ᵢ cᵢ eᵢ` of `𝓔` with coefficient vector `c` (Definition 2.8). -/
def eField (c : Fin 4 → ℝ) (x : Pt 2) : Pt 2 := ∑ i, c i • eBasis i x

/-! ### Explicit calculus for the eigenfields -/


                                                                                                 

                                                                                               
                                                      
                                                      
                                                           
       
                   

                                                                            
                                             

                                                                
                                                 

                                                                

                                                
                                                                                                          
                                                           

                                                                                  
                                       
                                                                    
                                                                                                 
                                                                                                 
                      
         
             
                     
                                                                    
                        
         
                                   
             
          
                     
                                                                    
                        
         
                                   
             
          

                                             
                                    
                                                                                                   
                                                                                                     
          
                                                                                               
                                                            

                                                                                              
                                                       
                                                          
                                                                
          
                                                                             
                                                                             
                     
                                                    
                                                                               
      
      

                                                                                          
                                                                                      

                                                                      
                
                                                             
                                                                     

                                                         
                     

                                                                 
                                    
                                                                                 
           
                                                      
                                                                     
                                                                
                                                       
              
                 

                                                                     
                                                                               
                                                                        
                                     
                                               

                                                                                   
                                    
                      
                                                                                                
                                  
                                          
                                               
                                                                                        

                                                                                       
                                                                                                      
                                                                               
                 
                                                                          
                                                                          
                             
       
                                                                                             
                                                    
             
                                                                        
                                                                        

                                                                                            
                                                                                            
                                        
                                               
                                                                                       
                                                                                              
                                                   
                                                        
                                    
                                 
                  
                                    
               
                                                         
                                                         
             
                  
                                                           
                                                
           
                                                                          
           
                  
                                                  
                                                    
                                                                                          
           
                                                    
                                                 
                                                                                                    
                                                      
            
             
                                   
           
                                                                            
         
                                                         
                    
                  
                                                             
                                                                                     
                         

                                                                               
                                                             
def IsFlowOf (b : ℝ → Pt 2 → Pt 2) (Φ : ℝ → Pt 2 → Pt 2) : Prop :=
  (∀ x, Φ 0 x = x) ∧ ∀ s x, HasDerivAt (fun s => Φ s x) (b s (Φ s x)) s


section MomentCorrection

                                                                    
                                                                          
                                                                    

variable {n : ℕ}

                                          
                                                                           
                     

                                                 
                                                                    
                                                       

                                                  
                                                                        
                                                      
                                       
                  
                                    
          
                                                              
          
                                                         

                                                                                  
                                          
            
                                             

                                                                        
             
          
                                                    
                                       

                                                                        
                                                 
       
                         
                  
       
                                                                     

                                                        
                                                                                        
                                                 

                                                                                   
                                                                      
                                                             
                                             
                                           
                                             
                                              
                                         
             
                                                                                                        

                                                                                               
                                                                                                    
                                       
                                                        

                                                                                      
                                            
                                                                                      
                                        
                                                 
                                             
                     
                                          
                                                  
             
                                                                                   
                                                                        
                                                         

                                                                                  
                                                      
                                                    
                                                                    
                                                    
            
                                          
                                            
               
                                                                  
               
                           
                                                                                      
                                   
                                                               
               
                 
                                                     
                                                       
                           
                                                                      
                                                                 
                                           
                                                                                        
               
                    
                                      
                                                
                                   
                                               
               
          

                                                                                            
                                                        
                                                                   
                                                     
                                                           
                                                    
                                                 
                                                                               
                             
                                           
                                       

end MomentCorrection

                                                                                    
                                                                                     
                                                                                              
                                                                              
                                                                                           
                                                                                               
                                                                      
                                                                            
                                                                            
                                                    
                                                                                
                                                
                                                                                  
                                                                 
                                                                                           
                                                                          
                
                           
                                                              
                             
                                                                        
                                                                
                                                   
                                                                
                                                                          
                                              
                                                           
                                    
                                                                       
                                             
                                                                       
           
                                                                                    
                                      
                                                
                                                              
                                 
                   
                                               
                                                                       
              
                                        
                                                            
                                                           
                                                          
                      
                     
                                           
           
                                                                                            
                                                                                       
                                         
                                                                          
                                               
                                                                                        
                                                                                                            
                         
                                                               
                                                                                        
                      
                                                                                              
                                                            
                                                                            
                                   



                                                                     
                                 
           
                              
         
                        

                                                                                        
                                                                                              
                                                                                           
                                                                                
                                                                                    
                                                        
                          
                                                                                              
                                                        
         
                          
                                                              
                                                      
                                                                              
                             
                                            
                                                                                   
                            
                                   
                                        
                                                                           
                                     
                                            
                                                  
                                                                                     
                                                                               
                                                                                        
                                                                                                  
                                                                                                  
                 
                 
                                   
                                                  
                                                  
                                                                                
                                    
                                                  
                          
                                                             
                                                                                               
                                                                                
         
                                                     
                                              
                                             
                                  
                                                                       
                                                
                                                                                        
                                                                              
                                                                                      
                                     
             
                                                                                     
                   
                                                          
                                                                                              
                 
                                                                    
            
                                                       
                                                
                                                                         
                                 
                           
                                              
                                                                       
                                 
                           
                             
                              
                                         
           
                        
                


                                      

                                                                      
def cNormE {d : ℕ} (a : ℕ) (h : Pt d → Pt d) : ℝ≥0∞ :=
  ⨆ x, ∑ k ∈ Finset.range (a + 1), ‖iteratedFDeriv ℝ k h x‖ₑ

/-- Euclidean operator norm of a linear map of `ℝ^d`. -/
def eucOp {d : ℕ} (A : Pt d →L[ℝ] Pt d) : ℝ :=
  ⨆ e : {e : Pt d // euclNorm e = 1}, euclNorm (A e.1)

/-- The data provided by **Lemma 2.13** for a fixed number `M` of vanishing moments and fixed
spatial bounds `S a`: a family of controls `b_ω(s) = ∑ᵢ coef ω s i • eᵢ ∈ 𝓔`, indexed by the
parameters `ω = (ιᵢ, zᵢ)_{i ≤ L}` of the block map, smooth in time and in the phases, supported
in a fixed compact subinterval of `(0,1)`, whose terminal flow map is the block map `𝓕_ω`, with
vanishing moments `∫₀¹ sʳ b_ω(s) ds = 0` for `0 ≤ r < M`, with `∫₀¹ ‖b_ω(s)‖_{C^a} ds ≤ S a`
(and `∫₀¹ ‖∇b_ω(s)‖_{L^∞, op} ds ≤ S 1`), and with all mixed derivatives bounded uniformly
in `ω`. -/
structure ControlFamily (L M : ℕ) (S : ℕ → ℝ) where
  coef : (Fin L → Bool × Pt 2) → ℝ → Fin 4 → ℝ
  a₀ : ℝ
  b₀ : ℝ
  ha₀ : 0 < a₀
  hab₀ : a₀ < b₀
  hb₀ : b₀ < 1
  support : ∀ w s, s ∉ Icc a₀ b₀ → coef w s = 0
  smooth : ∀ ιs : Fin L → Bool,
    ContDiff ℝ ∞ (fun p : (Fin L → Pt 2) × ℝ => coef (fun i => (ιs i, p.1 i)) p.2)
  terminal : ∀ w, ∃ Φ, IsFlowOf (fun s => eField (coef w s)) Φ ∧ Φ 1 = blockMap w
  moments : ∀ w, ∀ r < M, ∫ s in (0 : ℝ)..1, s ^ r • coef w s = 0
  bound : ∀ a w, ∫⁻ s in Icc 0 1, cNormE a (eField (coef w s)) ≤ ENNReal.ofReal (S a)
  bound_grad : ∀ w, ∫⁻ s in Icc 0 1, ⨆ x, ENNReal.ofReal (eucOp (fderiv ℝ (eField (coef w s)) x))
    ≤ ENNReal.ofReal (S 1)
  mixed : ∀ r : ℕ, ∃ C, ∀ w s, ‖iteratedDeriv r (coef w) s‖ ≤ C

/- **Lemma 2.13** (controls) is stated and proved as `controls_exist` in
`RequestProject/ControlsFinal.lean`, after the construction of the controls. -/

/-! ### The block parameter space and damped responses -/

/-- The single-block parameter space `Ω_b`: the `L` pairs `(ιᵢ, zᵢ)` and one extra global
translation `z₀ ∈ 𝕋²` (Definition 2.14). -/
abbrev BlockParam (L : ℕ) := (Fin L → Bool × Pt 2) × Pt 2

/-- The law on `Ω_b`: product of uniform measures (Definition 2.14). -/
def blockMeasure (L : ℕ) : Measure (BlockParam L) :=
  (Measure.pi fun _ : Fin L => stepMeasure).prod uniformTorus

instance (L : ℕ) : IsProbabilityMeasure (blockMeasure L) := by
  unfold blockMeasure; infer_instance

                                                                               
                                                                                      
                        
                                  

                                    
                                                                                    
                        
                                          

                       
                                                                         
                                                                                       
                                
                                                                                    


end AnomDiss
