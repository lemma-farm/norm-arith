module

public import AmbidextrousSofa.Measure.Fibers

@[expose] public section

/-!
# Integrated spatial partition and its equality conditions

This module passes from the pointwise identities to real Lebesgue integrals.
The horizontal projection is split into a measurable middle set and its
complement. Equal measure of those pieces cancels the constant terms. The
standard middle half of a closed interval is proved to have that property.

The resulting spatial scores are genuine integrals of roofs and barriers.
The exact identity holds even when some signed fibers are negative. Only
the final ordinary-area corollaries use nonnegative physical fibers and
measurable envelope containment. No universal sharp bound on a spatial
score is postulated or proved here.
-/

noncomputable section

open Set MeasureTheory

namespace AmbidextrousSofa

/-! ## The middle half has the required measure -/

/-- The middle half of the closed horizontal interval `[l,r]`. -/
def middleHalfInterval (l r : ℝ) : Set ℝ :=
  Icc (l + (r - l) / 4) (r - (r - l) / 4)

                                                    
                                             
                   

                                                           
                                       
                                            

                                                               
                                                            
                                                                   
      

                                                                        
                                                                      
                                                                                                
                                                                      
      

                                                                                   
                                                                    
                                          
                                                          
                                                                                    

                                            

                                                                                 
                                                                      
                                                   
                                         

                                                                                        
                                                                        
                                                                 
                                                                     

                                        
                                         
                                                    
                                                                                                
                                                                                         

                                                    

                                                                                     
                         
                                                                                
                                            
                                       
                                                                 
                                                    
                                                       
                                                         
                                                     
                                                                   
                                                     
                                                                               
                                                                   
                                     
                                               
                                                                                      
                                                                                          
                                                                                      
                                                                              
                                                                            
                                                      
                                                                                                     
                                
                                                     
          

                                                       

                                         

                                                                                        
                                                                             
                           
                                             
                                                               
                                                                        
                                                               
                                                                             
                                               
                                               
                                                         
                                                         
                                       
                                                          
                       
                                        
                                          
                                                   
                                                              
                                                                                          
                                                                                              
                                                                        
          

end AmbidextrousSofa
