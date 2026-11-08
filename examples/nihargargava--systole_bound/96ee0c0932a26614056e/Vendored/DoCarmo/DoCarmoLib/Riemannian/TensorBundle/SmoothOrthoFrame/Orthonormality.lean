module

/-
Vendored from frenzymath/Poincare-Conjecture (Apache-2.0).
Immutable commit: 5a9e2acd61c33320a2e6232e502d2189385f5157.
Original path: references/DoCarmo/DoCarmoLib/Riemannian/TensorBundle/SmoothOrthoFrame/Orthonormality.lean.
Original headers, namespaces and mathematical contracts are retained.
Local changes: import prefixes, upstream package-option restoration, and pinned API/linter compatibility.
See Code-Attribution.md and Vendored/DoCarmo/LICENSE.
-/
public import Vendored.DoCarmo.DoCarmoLib.Riemannian.Metric.RiemannianMetric
public import Vendored.DoCarmo.DoCarmoLib.Riemannian.TensorBundle.SmoothOrthoFrame.ChartBasis
public import Mathlib
@[expose] public section

-- Port: preserve the upstream DoCarmo package's elaboration options locally.
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 400000


/-!
# Orthonormality of the chart-frame Gram-Schmidt

Engineering proof chain for `chartFrameNormFiber_orthonormal` and
`chartFrameNorm_orthonormal`: the inductive $g$-Gram-Schmidt step
preserves orthogonality and unit length on the trivialization base
set.

The proof is by strong induction on the index $i.\mathrm{val}$; the
bundled IH carries three facts at every $i$: $\mathrm{raw}_i \ne 0$,
$\langle e_j, e_i\rangle = 0$ for $j < i$, and $\langle e_i, e_i\rangle
= 1$. Non-degeneracy of $\mathrm{raw}_i$ uses linear independence of
the chart-basis family (`chartBasisFamily_linearIndependent`) and the
inductive span identity
$e_0, \ldots, e_{i-1} \in \mathrm{span}(v_0, \ldots, v_{i-1})$.

Construction prerequisites live in
`Tensor/SmoothOrthoFrame/ChartBasis.lean`; the public bumped-section
API and `OrthonormalBasis` packaging live in the anchor
`Tensor/SmoothOrthoFrame.lean`.
-/

noncomputable section


open Bundle Manifold Set FiberBundle Filter
open scoped Manifold Topology ContDiff Bundle

namespace Riemannian
namespace Tensor

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-! ## Stage 3a: orthonormality of the un-bumped Gram-Schmidt frame

The inductive Gram-Schmidt step preserves orthogonality and unit length
on the trivialization base set. The proof is by strong induction on the
index $i.\mathrm{val}$; the bundled IH carries three facts at every
$i$: $\mathrm{raw}_i \ne 0$, $\langle e_j, e_i\rangle = 0$ for $j < i$,
and $\langle e_i, e_i\rangle = 1$.

The non-degeneracy step $\mathrm{raw}_i \ne 0$ uses linear independence
of the chart-basis family (`chartBasisFamily_linearIndependent`) and
the inductive span identity
$e_0, \ldots, e_{i-1} \in \mathrm{span}(v_0, \ldots, v_{i-1})$. -/

                                                                                     
                                                                             
                               
                                                             
                                                         
                 
                                                                             
           
                                            
                 
                         
                                                     
                                                               
                                                                                  
                   
                                                                              
                         
           

                                                                                     
                                                                             
                              
                                      
                                                         
                                        
                                                                             
           
                                            
                 
                         
                                                     
                                                             
                                                                              
                   
                  
                                                                              
                         
           

                                                                                     
                                                                     
                                                                     
                                                                   
                                                                    
                                             
                                           
                                                                         
                                                     
                    

                               
                                                                          
                                                                     
                                                                    
                                                             
                                                                     
                                                                 
                                                  
                                                     
                                              
                                    
                                             
                                  
                                            
                        
                                
                                         
                                                   
                           
          
                   
           
                       
                                                   
                                                        
               
                                    
                            
                               
                                           
                    
                       
                               
                               
                                 
                              
                               
                             
                                   
                                                   
                               
                 
                                
                                                               
                                        
                                        
               
                                                        
                                   
                                                           

                               
                                                                              
                                       

                                                                   
                                              
                                                                    
                                         
                                                                    
                                          
                                
                                              
                                                              
                                    
                                                 
           
                                
                                          
                                             
                                                    
                 
                                                  
                       
                                                      
                                             
                                                 
                                            
                                                   
                                                   
                         
                                                        
                                                 
                                                     
                                              
                                                         
                                                
                             
                                                        
                      
                              
                                       
                                                 
                         
              
                           
              
                            
                                                                  
                                                            
                                                      
                
                            
                                     
                                               
                   
                                           
                                             
                                                             
         
               
                        
                                                          
                         
                                              
                             
                                                                          
                           
                                                  

                                                             
                                                                             
                                                             

                                                                    
                                                                    
                                                          
                                                               
                                                 
                                                           
                                              
                                  
                                                
                                      
               
                                                
                                                   
                                  
                                                   
               
                                                
                                                         
           
               
                                                                      
                                  
                                      
                                                   
                                                          
                                                             
                                                                    
                                                                     
                                                              
                                                                
                                                                             
                  
                                                        
                                                
                                                             
                                                                   
                                                  
                   
                                                
                                      
                                                  
                                             
                       
                                                                     
                                                              
                                                          
                                               
                                                                 
               
                                                  
                                                              
                                
                                   
                                                                  
                                                
                          
             
                                              
                 
                                    
                                           
                                                        
                    
             
                                           
                                    
                        
           
                        
                                                                    
                                                
                                                   
               
                          

                               
                                                                   
                                                                  
          

                                                        
                                                    
                                   

                                                                      
                                                               
                                         
                                                                    
                                                                
                                                               
                                                   
                                              
                                                                
                                                        
                                               
                                                      
                 
                                                  
                                                         
               
                                                
                                                          
           
         
                  
           
                 
                                                   
                                                        
               
                       
                                                        
                
                
                                                            
                
                 
                              
                      
                                                                         
                                                                     
                                                   
                                                            
                     
                                                       
                                                             
                   
                                                    
                                                              
                  
                                          
                        
                                                                                
                                                             
                                          
                   
                                                    
                                                       
                                         
                               
                                                                  
                                          
                                                      
                                                               
                                
                    
                                          
                   
                         
                                      
                                                           
                                                     
                                                               
                                              
                                        
                                                                  
                                                                         
                                                                     
                                      
                                                                   
                                
                                               
                                                  
                                                             
                              
                     
                                                                   
                                 
                                                     
                                                           
                                                      
                                                  
                                                             
                                        
                                   
                                             
                                                     

                               
                                                                          
                                                                 
                         
                                                                    
                 
                                       
                                              
                                                              
                                      
             
                                              
                                                
                                  
           
                                                           
                                                                                     
                             
                                                              
                          
                                       
                                  
                                                                                       
                                                                                     
                                
                                                              
                           
                  

                               
                                                                              
                           
                                  
                                              
                                                              
                                      
             
                                         
                                           
                               
                                                     

end Tensor
end Riemannian
