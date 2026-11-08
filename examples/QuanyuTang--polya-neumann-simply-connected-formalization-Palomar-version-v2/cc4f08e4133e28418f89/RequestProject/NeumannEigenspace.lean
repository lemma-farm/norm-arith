module

public import RequestProject.Rellich
public import RequestProject.Finite

/-!
# Neumann eigenspaces

The Neumann eigenspace `ker(A_N - E)` of a domain `Ω` is the space of `u ∈ H¹(Ω)` satisfying the
weak Neumann eigenvalue equation `∫_Ω ∇v̄ · ∇u = E ∫_Ω v̄ u` for every `v ∈ H¹(Ω)`
(`neumannEigenspace`).

For a bounded Lipschitz domain it is finite-dimensional (`finiteDimensional_neumannEigenspace`,
the finiteness statement of Lemma 3.3): its elements satisfy `‖∇u‖² = E ‖u‖²`, so a bounded
sequence in it is bounded in `H¹(Ω)`, and Rellich compactness rules out the separated
sequences that an infinite-dimensional normed space contains (Riesz's lemma).
-/

@[expose] public section

open MeasureTheory Filter Topology

noncomputable section

namespace PolyaNeumann

                                                                                             
                                                                                       
                                       
                                                                    
                                                                           
                                                       
                                                             
                
                                      
                                               
                                                                                           
              
                 
                          
                                               
                                                                            
        

                                                  
                                                                          
                                                  
                                                                                         
                                                   
                     
                                                               
                                                  
                                                    
                                                        
                                             
                                            
                                                                
                                                                         
                                                                                 

                                                                                              
                      
                                                                                    
                                                                                          
                
                                                                         
                                                                                       
                                                                                     
                            
                                                                       
                             
                                                                     
                                                                                      
                                                               
                                                                                      
                              
                                      
                                     
                                           
                                                          
                         
                                 
                                                
          

end PolyaNeumann
