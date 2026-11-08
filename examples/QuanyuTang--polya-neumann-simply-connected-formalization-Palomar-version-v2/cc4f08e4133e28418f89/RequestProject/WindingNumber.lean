module

public import RequestProject.GreenWinding

/-!
# Winding numbers of closed Lipschitz curves

For a closed Lipschitz curve `γ` (`γ(2π) = γ(0)`) and `z ∉ γ([0, 2π])`:

* `PolyaNeumann.windingNumber_mem_range_intCast`: the winding number is an integer;
* `PolyaNeumann.continuousOn_windingNumber`: it is continuous off the curve;
* `PolyaNeumann.windingNumber_eq_zero_of_far`: it vanishes far from the curve;
* `PolyaNeumann.windingNumber_const_of_isPreconnected`: it is constant on preconnected sets
  avoiding the curve.
-/

@[expose] public section

open MeasureTheory Set Filter Metric
open scoped ComplexConjugate Real Topology

noncomputable section

namespace PolyaNeumann

                                                                                           
                                                                                 
                                                                                            
                                                                                                  
                                                            
                                                                                      
                                                        
                                                            
                                                                                      
                                                        
                                                                 
                                                                 
                                                         
                                               
                                                                 
            
                                                     
           
                                                                                         
                                                                                         
                                                               
                                                              
          
                                                                             
                      
                                      

                                                                      
                                               
                                                                                   
                                                                         
                                                              
                                                         
                                                              
                                                                              

                                                                                    
           
                                                                                         
                                                                       
                                                 
                                             
                                                    
                                                
                                                                            
                                                      
              
               
                 
                                                                 
                                                                                     
                                                      
                                                                                
                                     
           
                                   
                                            
                                                                                         
                                                            
                                                 
                                           
                                                             
                                                          
                                                                                           
                                                                                        
                                                                  
                                                              
                                                                        
                                
                                                                             
                                
              
                       
                                
              
                                                         
                        
            
              
        
                                                                               
              
                                
                                          
                                 
                                                                          
                                                                                       
                                            
                                                                                         
                                                                       
                                                           
                                                                            
                                                                                   
                                                                           
                                                       
                                                                               
                                                                                         
                   
                               
            
                                   
                              
            
                                                                 
                                                       
                                                   
                                                              
                                        
                                                         
                                
                                
                 
                                                                                              
                       
                                             
                                             
           
            

                                                      
                                                                                      
                                                              
                                             
                                                    
                                                
              
                                                                              
                                                                                 
                   
                                  
                 
                   
                                                                   
                                                         
                                     
                                              
                         
                                                      
                                                                 
                  
                                           
                      
                                  
                                                                                            
                                     
                                                                 
                                                                           
                                                             
                                              
                             
                 
                                                                                      
                                   
                                              
                             
                                 
             
                                                                     
                               
              
                                                                             

                                                                                        
                                                                    
                                                                                      
                                                                  
                                                                            
                                                    
                                        
                       
                    
                                    
            
                                                                 
                                             
                                                                                            
                                                                              
                                           
                                      
                   
                                                                                 
                                          
                                                       
                                                                                           
                               
              
                                                        
                                                                     
                                                    
                                
                                      
                       
                            
                                                                                 
                         
                                                    
                                                                        
                          

lemma isometry_intCast_complex : Isometry ((↑) : ℤ → ℂ) := by
  refine Isometry.of_dist_eq fun m n => ?_
  rw [Complex.dist_eq, Int.dist_eq, ← Complex.ofReal_intCast, ← Complex.ofReal_intCast,
    ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]

instance : DiscreteTopology (range ((↑) : ℤ → ℂ)) :=
  isometry_intCast_complex.isEmbedding.toHomeomorph.symm.isEmbedding.discreteTopology

                                                                                        
                      
                                                                      
                                                                                            
                                                                                 
                                               
                                                                                  
                                                                                 
                                               
                                                                            

end PolyaNeumann

end
