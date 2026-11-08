module
-- Reversible module-visibility port of the audited development.
/-
Selected proof slices adapted from Scott McColm, MIT-0,
commit 6e2d10c6c2252ee1575bb7ef12dea12e2f1a3af1.
See ../../../../../third_party/twelfth/SOURCE_IMPORTS.json and LICENSE-MIT-0.
No upstream project or Architect module is imported.
-/
public import MathCollab.Density.DivisorGrowth
public import Mathlib
public import Mathlib.Analysis.SpecialFunctions.Pow.Complex
public import Mathlib.Tactic

-- BEGIN MODULE VISIBILITY
@[expose] public section
-- END MODULE VISIBILITY

open Complex Set Finset MeasureTheory Filter
open scoped BigOperators Interval ComplexConjugate
set_option autoImplicit false
noncomputable section
namespace MathCollab.Density.Stronger.Fourth

                                              
                       
noncomputable def afeCriticalPoint (t : ℝ) : ℂ := (1 / 2 : ℂ) + (t : ℂ) * I
                                                         
                                                             
                                                       

                                                                      
                                                             
                                                      
                     
                              
                                            
                                           
                        
      


                                                              
                                                                      
                                                
                     
           
                               
                                                                 
                                                               
                                                
                                                                                  
         
                             


                                          
                                      

                                                                    
                                             

                                                                   
                                                                                     

                                              
                                                                      
                                                                                         


                                                                
                                                      
                                                   
                                                                                              
                                             
                              
                 
                                              
                                              
                                                                  
                             
        
                                             
                                                              
                                                         
      
                                    
                                              
                                 
                                                 
             
              
          
                          
                               
                                                                          

                                                       
                          
                                                               
                                              
                                         
                                           
              
                                                                         
                                                                             
                                            
                                  
                                                                                
      
                                                       
                              
               
                                                            
                                      
              
                

                                                                      
                                                      
                                                           
                           
                                                              
                                                                                        
                   
                 
      
                                                  
                                                  
                                            
                                                                             
                        
                                                                           

end MathCollab.Density.Stronger.Fourth
