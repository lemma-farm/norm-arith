module

public import AmbidextrousSofa.Geometry.CapGeometry

@[expose] public section

/-!
# Support functions of actual planar sets

The support is defined directly from the coordinate dot product and a real
supremum. Compactness supplies boundedness and attainment; none of those facts
is stored as an extra certificate. Convex-hull invariance is proved from the
minimality of the actual convex hull. Upward support is preserved by downward
filling, which is the support identity needed by the scalar cap reduction.
-/

noncomputable section

open Set

namespace AmbidextrousSofa

/-- Euclidean coordinate pairing, independent of the product norm. -/
def coordDot (p v : Plane) : ℝ := p.1 * v.1 + p.2 * v.2

                                                                                                  
                                                        

                                                                                              
                                                                       

                                                                                               
                                                                       

theorem continuous_coordDot_right (v : Plane) : Continuous (fun p => coordDot p v) := by
  unfold coordDot; fun_prop

                                                                            
                           

                                                                                          
def support (K : Set Plane) (v : Plane) : ℝ := sSup ((fun p => coordDot p v) '' K)

                                                          

                                                              
                                                                        

theorem support_bddAbove {K : Set Plane} (hK : IsCompact K) (v : Plane) :
    BddAbove ((fun p => coordDot p v) '' K) :=
  hK.bddAbove_image (continuous_coordDot_right v).continuousOn

theorem coordDot_le_support {K : Set Plane} (hK : IsCompact K) {p : Plane}
    (hp : p ∈ K) (v : Plane) : coordDot p v ≤ support K v :=
  le_csSup (support_bddAbove hK v) (mem_image_of_mem _ hp)

                                                                                      
                                                                     
                                                                           
                                                                 

                                                                                   
                                                        
                                               

                                                                       
                                                                 
                                                                       

                                                                                
                                                              
                                                 
                                                                                 

                                                                                         
                                                                                  

                                                                                       

                                                                                                   
                                                    

                                                       
                                              
                                                                                                 

                                                            
                                                                                
                                                              
                                                                 
                                                                                            
                                                             
                                                                                
                                                                                          

                                                                                         
                                                                             
                                                           
                                                         
                                                                
                 
                                                                                         
                                       
                                                
                                                                                        
                       
                                    
                                        
                                                              
                                       

                                                                                               
                                                                                 
                                                                  
                                                                                 
               
       
                                                                 
                                                                  

                                                                                 
                                                                              
                                                         
                                              
                                                                               
                                                                          
                          
                                                     
                                                                                               

                                                                                   
                                                            
                                                     
                                

                                                                             
                                                                               
                                                                                        
                                                            
                                                                              
                                    
                       
                        
                                                       

                                                                                    
                                                                                
                                                            
                                                                                    
                          
                                                                  

                                               
                                                              
                                                                

                                                                                        
                                                            

                                                                              
                                                                                               

                                                                                             
                                                                                                   

                                                                                       
                                               
                                                     
                                                 
                                                                           
                                                                            
                                                                                            

                                                                                    
                           
                                                 
                                                                              

end AmbidextrousSofa
