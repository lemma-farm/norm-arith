module
-- Reversible module-visibility port of the audited development.
/-
Selected proof slices adapted from Scott McColm, MIT-0,
commit 6e2d10c6c2252ee1575bb7ef12dea12e2f1a3af1.
The fixed-strip growth and Gaussian contour majorants are new proofs.
See ../../../../../third_party/twelfth/SQUARE_GROWTH_MANIFEST.json
and ../../../../../third_party/twelfth/LICENSE-MIT-0.
No global-order, Hadamard, Architect, or upstream project module is imported.
-/
public import MathCollab.Density.Stronger.Fourth.SquareSource
public import MathCollab.Density.AbelZetaGrowth
public import Mathlib

-- BEGIN MODULE VISIBILITY
@[expose] public section
-- END MODULE VISIBILITY

open Complex Filter MeasureTheory Set Topology
open MathCollab.Density.Stronger.Fourth MathCollab.Density.ZetaGrowth
open MathCollab.Density.Contour
open scoped Interval
set_option autoImplicit false
noncomputable section
namespace MathCollab.Density.Stronger.Fourth

                                                            
                                             
                                                              
      
                            
                                                        
                               
                                                            
                                                    
                               
                                            
                                           
                                                                                
                                                                              
                                                
                                                          

                                                                         
                 
                                                             
                        
                                                         
                                   
                                                    
                                            
                                             
                                   
                
            
                                                 
                                          
                                             
          
                        
                                                        

                                                                             
                                                            
                                                                   
                                                                   
                                                                         
                                                                   
                                                      
                                                           
                                                                   
                                                                           
                                                      
                                                     
            
                                                              
                                                   

                                                                            
                                                          
                 
                                                                 
                                                                 
                                                  
                        
                                      
                        
                                      
                                             
                                                                                 
                         
                                      
                                                                 
                                                                                      
                                 
      
                                                              
                    

                                                                                    
                                                                            
                                                           
                                                  
                                                       
                                         
                                  
                 
                            
                          
                                                                
                                             
                                       
                                                
                                                                   
                                                    
                                                                        
                                          
                                       
                                      
                    
                              
        
                              
                                        
                      


                                                                                     
                                                                      
                                              
                                                  
                                                                          
                                                                       
                                                                      
                                            
            
                           
                                                                   
                            
                                                                                       
                                                                                    
                                                                         
                                                                
                                                                        
                                                                    
                                             

end MathCollab.Density.Stronger.Fourth
