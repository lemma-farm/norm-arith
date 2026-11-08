module

public import RequestProject.WeakConstancy
public import RequestProject.Finite

/-!
# Weak compactness in `L²` and uniqueness of weak gradients

* `exists_weak_subseq`: a bounded sequence in a separable Hilbert space has a weakly convergent
  subsequence (sequential Banach–Alaoglu together with the Riesz representation).
* `separableSpace_L2`: `L²(Ω)` is separable.
* `IsWeakGradient.unique`: on an open set, the weak gradient of an `L²` function is unique.
* `neumannEnergy_eq_of_isWeakGradient`: the Neumann energy is `∑ ‖gᵢ‖²` for the weak gradient.
-/

@[expose] public section

open MeasureTheory Filter Topology

noncomputable section

namespace PolyaNeumann

                                                                             
                                                                                     
                                                                             
                           
                                                 
                                                                          
                                                                               
                                                     
                                                                                       
           
                  
                                     
                                                                                            
                                                             
                                                        
                    
         
                                   
                                                                         
                                                              
                          
                                              

                            
instance separableSpace_L2 (Ω : Set ℂ) : TopologicalSpace.SeparableSpace (L2 Ω) := by
  haveI : Fact ((2 : ENNReal) ≠ ⊤) := ⟨by simp⟩
  haveI : SecondCountableTopology (L2 Ω) := Lp.SecondCountableTopology
  infer_instance

                                                                      
                                                                                     
                                             
          
                                                                    
                                                                                         
                           
                                                            
                                                                               
                                                                 
                          
                                                                                        
                                
                                                      
              
                                                                          
                       
                                         
                                                                    
                                                                          
               
                           
                                                
                   
                 
                                                   
              
                                                             
                                                                                             
                                     
                           
             
     

                                                       
                                                                                          
                                                                            
                                  
                                                                        
                                                            

                                                                                         
                                                                                 
                                                    
                                                         
                   
                       
                                                         

end PolyaNeumann

end
