module

public import SubdiffusiveProcess.DirichletForm.Resolvent
public import Mathlib.Analysis.InnerProductSpace.Dual

@[expose] public section

/-!
# Every closed form has a resolvent

For a closed form `E` on `L²(m)` and `α > 0` the domain with the inner product
`α⟪u, v⟫ + E(u, v)` is a Hilbert space (this is the closedness of `E`); the Riesz representation of
`v ↦ ⟪f, v⟫` is the resolvent `G_α f` (Fukushima–Oshima–Takeda, Thm 1.3.1's Lax–Milgram step).
-/
open MeasureTheory Filter Topology
open scoped RealInnerProductSpace
noncomputable section
namespace SubdiffusiveProcess.E7
open _root_.SubdiffusiveProcess.DirichletForm

variable {X : Type*} [MeasurableSpace X] {m : Measure X}

/-- The domain of a closed form with the inner product `α⟪u,v⟫ + E(u,v)` (type synonym). -/
def ShDom (E : ClosedForm m) (_α : ℝ) : Type _ := ↥E.domain

instance (E : ClosedForm m) (α : ℝ) : AddCommGroup (ShDom E α) :=
  inferInstanceAs (AddCommGroup ↥E.domain)

instance (E : ClosedForm m) (α : ℝ) : Module ℝ (ShDom E α) :=
  inferInstanceAs (Module ℝ ↥E.domain)

namespace ShDom

variable {E : ClosedForm m} {α : ℝ}

def val (u : ShDom E α) : Lp ℝ 2 m := (u : ↥E.domain).1

                                                                       

                                                                              

                                                                                             

                                                                              
                                                                              
                                                                  
                                                                                 
                                                         

theorem ext {u v : ShDom E α} (h : u.val = v.val) : u = v := Subtype.ext h

end ShDom

                                      
                     
                                                                                               
                                                           
                           
                                                                         
                                                  
                                                                           
                         
                                                                     
                          
                                                                                          
                      
                                                                   
                                                      
                                                      
                                                                                           
        
                       
                                                                   
                                                                        
                                                                                                       
        
                     
                                                                     
                                            
                                             
                                                                 
                                           
                                                       
                                          
                             
               
                                             


                                                                                                  
                                       
                                                                    
                                                          
                     
                                         
                                                                                  
                                          
                                                 
                                                                                          
                                     
                                                         
                                   
                                                                                          
                                        
                                                              
                                               
                                                                                       
                
                                                                                             
                         
                                     
                              
                             
                                                    
                                                                 
                                                      
                               
                                     
                                                                                   
                                                              
               
                               
                                         
                                                                                        
                
                              
                                          
                                                                             
                                                              
                                                
             
                                             
                                       
                                                     
                                                                              
                                                     
                               
                                 
                             
                                      
                    
                                                                                                  
           
                                
                                         
                                                        
                                                                 
                                                                       
             
                                           
                             
                                            
                                                 
                                                              
                                                
                           
                                                               
                                                      
                                      
                                                                          
                                        
                                                                            
                                                                        
                                                                          
                                             
                       
                                                               
                                        
                                                   
                                                                    
                                        
                                                 
                                     
                                 
                                                  
                                                      
                                                 
           
                                                   
                                           
                                                   
                                    
                                                                               
                        
                                                          
                           
                                        
                      
                        
                                                    
                                                  
              
                                                                                   
                              
            

end SubdiffusiveProcess.E7
