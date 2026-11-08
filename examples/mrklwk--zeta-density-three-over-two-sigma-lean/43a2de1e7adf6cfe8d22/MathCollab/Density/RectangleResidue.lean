module
-- Reversible module-visibility port of the audited development.
/-
Selected rectangle geometry and single-pole residue proofs from McColm's
External/PNT/{Rectangle,ResidueCalcOnRectangles}.lean at exact revision
2ace9e7c09a69fdcd1edae1ab6deb7cb3b4df1be. Adapted upstream PNT+ code,
Apache-2.0; copyright belongs to its contributors. Existing notice retained.
No general residue machinery or upstream project module is imported.
-/
public import Mathlib
public import Mathlib.Analysis.Complex.Convex
public import Mathlib.Analysis.Complex.RemovableSingularity
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.Tactic

-- BEGIN MODULE VISIBILITY
@[expose] public section
-- END MODULE VISIBILITY

open Complex BigOperators Nat Classical Real Topology Filter
open Set MeasureTheory intervalIntegral
open scoped Interval
set_option autoImplicit false
noncomputable section
namespace MathCollab.Density.Contour

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {f g : ℂ → E}
  {z w p c A : ℂ} {x x₁ x₂ y y₁ y₂ σ : ℝ}

                                        
                                                       
                                                       

                                                                                          
                       
                                                                 
                                                              
                 

                                                             
                                                                       

                                                              
                                                                         

                                                                              
                                        

                                                                               
                                         

                                                                                              
            
                                
                                    
                                    
                                     
                                     

                                                      
                                                                 
                                            
                                        
                                                  
                                                                             
                        

                                            
                                                                                
                                                                                         
                 

                                                  
                                                                                  
                                                
                                                     

                                                   
                                                                                  
                                                
                                                     

                                                  
                                                                                 
                                                
                                                       

                                                   
                                                                                 
                                                
                                                       

                                                                 
                                
                                 
                                                                          
                                         
                                                                     
                                                                

noncomputable def HIntegral (f : ℂ → E) (x₁ x₂ y : ℝ) : E :=
    ∫ x in x₁..x₂, f (x + y * I)

/-- The `VIntegral` definition used by the source-facing construction in `ResidueCalcOnRectangles`. -/
noncomputable def VIntegral (f : ℂ → E) (x y₁ y₂ : ℝ) : E :=
    I • ∫ y in y₁..y₂, f (x + y * I)

                                                                                                       
                                                             
                                           

                                                                                                       
                                                             
                                           

noncomputable def RectangleIntegral (f : ℂ → E) (z w : ℂ) : E :=
    HIntegral f z.re w.re z.im - HIntegral f z.re w.re w.im +
    VIntegral f w.re z.im w.im - VIntegral f z.re z.im w.im

                                                                    
                                                              
                                                                    
                                               

                                                      
                          

                                                           
                                            
                              
                                  
                                                          
                    

                                                                          
                                                           
                                    
                                  
                                                
                                                        
                                              
                                    
                                                        

                                                                           
                                                             
                                                    

def RectangleBorderIntegrable (f : ℂ → E) (z w : ℂ) : Prop :=
    IntervalIntegrable (fun x => f (x + z.im * I)) volume z.re w.re ∧
    IntervalIntegrable (fun x => f (x + w.im * I)) volume z.re w.re ∧
    IntervalIntegrable (fun y => f (w.re + y * I)) volume z.im w.im ∧
    IntervalIntegrable (fun y => f (z.re + y * I)) volume z.im w.im

theorem RectangleBorderIntegrable.add {f g : ℂ → E}
    (hf : RectangleBorderIntegrable f z w) (hg : RectangleBorderIntegrable g z w) :
    RectangleIntegral (f + g) z w = RectangleIntegral f z w + RectangleIntegral g z w := by
  dsimp [RectangleIntegral, HIntegral, VIntegral]
  have h₁ := intervalIntegral.integral_add hf.1 hg.1
  have h₂ := intervalIntegral.integral_add hf.2.1 hg.2.1
  have h₃ := intervalIntegral.integral_add hf.2.2.1 hg.2.2.1
  have h₄ := intervalIntegral.integral_add hf.2.2.2 hg.2.2.2
  rw [h₁, h₂, h₃, h₄]
  module

                         
                                                                                             
                                      
                                                                                   
                                                                                     
                                                                                     
                                                                                    

                         
                                                                                      
                                      
                                                                                          

                         
                                                 
                                                                                          
                                         
                                                                                    
                                                                                         

                                                
                                                                                
                                      
                                                                                                              

                                                                                        
                                                                                             

                                                             
                                                                                          
                                                                   
                                               
                                                      

                                                              
                                                                                            
                                                           

                                                                                   
                                      
                                               

                                                                
                                           

                                                    
                                              
                                                                                                 

                                                  
                                        
                                                                       
                                                   
                                                                                 
                                                          
                                                               
              
                                                                                
                                                                                             
                      
                                                                                          

                                                   
                                        
                                                       
                                                                  
                                                                                
                                  
                                    
              
        

                                                        
                                                     
                                        
                                                                         
                                                               
                                                                                                 
           
                                   
        
                                                                                   
                                       
                           
             
                                                                                          
                                                                                       
                                       
                                                           
             
                              
                                                                             
           
                                                                                 
                                                                    

                                                     
                                        
                                                                                   
                                                                     
                                                                   
                                 
                    
                                 
                                     
                    
                                 
                  
             
           
        
                                          
                                                 

                                           
                                                                     
                                                                
                                                                  
                                                                                      
                                                                                      
                                                         
                                                                                
                                                         
                                                                            
                                                         
                                                                                
                                                         
                                                              
         
                                                                                     
                   
                                     
         
                                                                                            
         

                                 
                                                         
                                             
                                                           
                                                                                  
                                             
                                                       
                                                      
              
                               
                    

                                                                           
                                                         
                                                                                     
                                                                                  
                                      
                                                                                       
                                                                                      
                                                                        
                                               
                                            
                                    
                                                                          
                                    
                                              
                                   
                                                                           
                                           
                                
                                      
                                                                                 
                            
                          
                  
                      
              
                                                                  
                                                               
                                                                        
                                                              
                                                                       


end MathCollab.Density.Contour
