module
public import Mathlib
                                                 
                                    

/-!
# Finite trapping by a pointwise integral argument

`Lovasz.Trapping.finite_trapping`: let `G` be a Hausdorff topological group with a left Haar
measure and `U` a symmetric open identity neighbourhood with compact closure.  For every `a ≥ 0`
there is an open identity neighbourhood `V ⊆ U` such that, whenever `Q` is symmetric, contains
`1`, is contained in the union `Q(V)` of all subgroups inside `V`, and `Qⁿ ⊆ U` with `n ≥ 1`, then
`Q^(a n) ⊆ U⁴`.

The proof uses the finite averages of layer indicators
`ψ = (1/n) ∑_{j<n} 1_{Qʲ U}` and `η = (1/M) ∑_{j<M} 1_{Wʲ U}` (`FiniteTrappingLayers.lean`), and
the function `φ(x) = ∫ ψ(y) η(y⁻¹x) dμ(y)`.  All estimates are pointwise; no continuity of the
convolution and no measurability of `Q` is used.
-/

@[expose] public section

open scoped Pointwise Topology
open MeasureTheory

namespace Lovasz.Trapping

variable {G : Type*} [Group G]

                                                          
                                             
                                                 

                                                                                           
                             
                            
                             

                                                 

variable [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G] [MeasurableSpace G] [BorelSpace G]

section Integrals

variable (μ : Measure G) [IsFiniteMeasureOnCompacts μ]

omit [Group G] [IsTopologicalGroup G] in
/-- A measurable function bounded by `c` on a compact set `K` and vanishing off `K` is integrable,
with `|∫ F| ≤ c μ(K)`. -/
lemma integrable_and_abs_integral_le {F : G → ℝ} (hF : Measurable F) {K : Set G}
    (hK : IsCompact K) {c : ℝ} (hbound : ∀ y ∈ K, |F y| ≤ c) (hzero : ∀ y ∉ K, F y = 0) :
    Integrable F μ ∧ |∫ y, F y ∂μ| ≤ c * μ.real K := by
  have hKm : MeasurableSet K := hK.measurableSet
  have hle : ∀ y, ‖F y‖ ≤ K.indicator (fun _ => c) y := by
    intro y
    by_cases hy : y ∈ K
    · rw [Set.indicator_of_mem hy, Real.norm_eq_abs]; exact hbound y hy
    · rw [Set.indicator_of_notMem hy, hzero y hy, norm_zero]
  have hint : Integrable (K.indicator fun _ => c) μ :=
    (integrableOn_const (hK.measure_lt_top.ne)).integrable_indicator hKm
  refine ⟨hint.mono' hF.aestronglyMeasurable (Filter.Eventually.of_forall hle), ?_⟩
  have := norm_integral_le_of_norm_le hint (Filter.Eventually.of_forall hle)
  rw [integral_indicator_const _ hKm, smul_eq_mul, Real.norm_eq_abs] at this
  linarith

                                                                   
                                                                             

            

                   
                                                                                               
                                            
                                                                   

                                                                                     
                                                                                        
                                                                                      
                                                                                 
                                                                
              
                                       
                                                                                
                      

                                                                                          
                                                      
                                                                           
                                                                                        
                                               
                                                       
                                                           
             
                                                                       
                                                        
                                                                         
                                                                                
                                                                              
                                       
                         
                                                                                   

                               

                                                                                          
                                                                                   
                                                                                        
                                                                        
                                        
                                                                                       
                                                                           
               
                                                                           
                  
                                                           
                                                                                  
          
             
                                                                       
                                                                       
                      

end Integrals

                            

section Core

                                          

                                                      
                                                                               
                                                    
                                                                

                                                                                                 
                                                                                                
                                                                                        
                                                                     
                                                                                              
                                                                                             
                                                                         
                                                                                   
                                                                      
           
                                     
                                                     
                                                     
                           
                                                                                 
                                                                                 
                                                         
                                                
                                                      
                                                                         
                                                                         
                                                                         
                                                                                        
                                   
                                
                                          
                                                     
                                                      
                           
                            
                                                                              
                                                      
                                          
              
                                                 
                
                                  
                                                          
                                                                          
                                            
                                                                            
                                                                
                
                                                                  
                                                                    
                                   
                                                                
                
                           
                            
                                                                              
                                                      
                                          
              
                                                 
                
                                  
                                                          
                                            
                                                                            
                                                                
                
                                                                  
                                                                    
                                   
                                                                
                
                                      
                                                           
                     
                                             
                        
         
                     
                                
                                                  
                                                  
                                        
                                                            
                
                                                                       
                                      
                                      
                          
                                  
                                                                                     
                     
                                              
                
                                             
                                                                   
                                                    
                                                                   
                                                                         
                                                       
                                                   
                                                               
                                        
                                                                              
                                      
                                              
                                      
                                       
                                                                        
                
                                                          
                                                          
                                                             
             
                                                                
                                             
                                                             
                                                                                    
                                                                     
          
                                           
                                                                            
                                                                                         
                                                     
                                                          
                                                 
                                                                 
                                        
                                               
               
                                      
                                                                          
                                                         
                                            
                                        
                    
                                    
                                                     
                                      
                                
                        
                                                                                           
           
                    
             
                  
                                      
              
          
                  
                  
                         
                                        
                                                            
            
                                       
                                                                                            
                                                                                              
                                                                       
                                         
                                 
                                                                            
                                                               
                                                         
                                                                 
                                                                       
                                                 
                         
                                                                                  
                                       
                                                                         
                                                                                    
                                              
              
                 
            
                                                          
              
                   
                                                
                                             
                                              
               
                                    
                                                  
                                        
                            
               
            
                               
                                                         
                                                                     
                        
                                   
                               
            
                                
                      
                                                                 
                                

            
                                                                                                
                                                                                                            
                                                                                                 
                                                                                           
                  
                                                                                                  
                                           
                                                           
                                                                     
                                                              
                                   
                                              
                                                                
                              
                                                   
                                                                                  
                                         
                           
                                        
                                                     
                             
                                            
                         
                                                 
                                     
                                                              
                                                                                
                               
                                
                                                                    
                                                                       
                                                 
                                
                               
                                                    
                                                    
                                                                               
                                    
             
             

end Core

                                                                                                 
                                                                                       
                                                                                                   
                                                                                    
                                                                                         
                                                                                        
                                                             
                                                           
                                                                     
                                                              
            
                                                                              

end Lovasz.Trapping
