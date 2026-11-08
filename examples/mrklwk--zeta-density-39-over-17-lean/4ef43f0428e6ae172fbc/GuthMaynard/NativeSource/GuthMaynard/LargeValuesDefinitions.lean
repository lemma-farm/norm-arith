module
public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Analysis.Calculus.ContDiff.FTaylorSeries
public import Mathlib.Analysis.SpecialFunctions.Pow.Complex
public import Mathlib.Data.Finset.Prod
public import Mathlib.Analysis.Normed.Group.Bounded
                                                                            
                                                                      

@[expose] public section

open Complex Finset Set
open scoped BigOperators ContDiff

namespace GuthMaynard.NativeMoment

/-!
# Source-facing objects for Guth--Maynard large values

These are the finite objects used by Sections 3--12 of Guth--Maynard.  They
replace the unrelated and false parabola-decoupling model formerly present in
the project.  No analytic estimate is postulated in this file.
-/

/-- A fixed smooth cutoff supported on the source dyadic interval.  Derivative
bounds are recorded separately by the lemmas that consume a cutoff, so that
their constant dependencies remain visible. -/
structure GMSmoothCutoff where
  /-- The `toFun` component of `GMSmoothCutoff`. -/
  toFun : ℝ → ℝ
  smooth : ContDiff ℝ ∞ toFun
  nonneg : ∀ x, 0 ≤ toFun x
  bounded : ∀ x, toFun x ≤ 1
  support : Function.support toFun ⊆ Set.Icc 1 2
  equals_one : ∀ x ∈ Set.Icc (6 / 5 : ℝ) (9 / 5 : ℝ), toFun x = 1

instance : CoeFun GMSmoothCutoff (fun _ => ℝ → ℝ) := ⟨GMSmoothCutoff.toFun⟩

                                                                             
                                      
                                                             
                                                                  
                                                          
                                                       
           
              
                      
                
                 
                 
                       
           
                                                                
                           
                                                   
                                
                                
                                 
           
                               
                                         
                                      
                                 
                  
                                 
              
                                             
                            
                      
                              
                            
                            
                                          
                                              
                                         

                                                                            
                                                                           
                                                                           
                                  
                                                  
                                       
                    
                                                        
                                                   
                                                                              
                      
                                                            
                             
                                                                    
                                           
                                                              
                   
                                                                       
                                        
         
                                                              
                                           
                                                             
                   
                                   
                 

                                                                            
                                               

                                                                   
                                                          

                                                         
                                                                 
                                                        
                                                

                                                                              
                                                                         
                              
                         
                                                        

                                                                 
                                                   
                                          

                                                                        
                                                                        
                                 
                                        
                                       

                                                                             
                                                                              
              
                                                               
                                          

                                                                   
                    
                                                                                
            
                                                              
                               
                             

                                                                      
                                                    
                                                                     

                                                                            
                                 
                                           
                                                                
            
                                                 

                                                       
                                            

                                                                 
                                          
                                                      
      
                                           
                                                 
                                                                  
                                                              

                                                                        
                                          
           
                                              
                                  
                                                          
                    
                                        
                 
                               
                                                                   
              
                                                     
                               
                               
                                                                
                                 
                                       
      
                                                   
                                           
                                                                               
                                  

                                                       
            

                                                                     
                                                              
                            
          
      
                                                
                                                     
                     
                               
                                
                
                                                               
          
                         

                                                                 
                                                            
                                        
                         
                            
            
                                        
                                                   
                                              
                              
               
                                                          
              
                                                         
                                                              
            
                                             
                         
                                                                   
                       
                              

                                                                 
                                     
                                       

end GuthMaynard.NativeMoment
