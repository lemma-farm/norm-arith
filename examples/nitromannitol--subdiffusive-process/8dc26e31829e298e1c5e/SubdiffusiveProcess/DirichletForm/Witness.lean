/-
# Inhabitation witnesses for every structure of the library
-/
module

public import SubdiffusiveProcess.DirichletForm.ImageDensity
public import SubdiffusiveProcess.DirichletForm.Weighted
public import SubdiffusiveProcess.DirichletForm.Gradient
public import SubdiffusiveProcess.DirichletForm.Killed
public import SubdiffusiveProcess.DirichletForm.Resolvent
public import Mathlib
@[expose] public section

/-!
# Inhabitation witnesses

Every structure of this library is inhabited; this file provides the witnesses,
and each structure's docstring names its witness on an `Inhabited by:` line.
The point is not that the witnesses are interesting — they are the **zero form**
`E = 0` with `D(E) = L²(X, m)` — but that no structure is vacuous, so that a
theorem taking one of them as a hypothesis is not vacuously true.

## Honest limits of these witnesses

The zero form is degenerate.  A *nonzero* witness would be the Dirichlet form of
the Laplacian on `ℝ^d`, i.e. `E(u) = ∫ |∇u|²`, whose energy measure is
`|∇u|² dx`.  **Mathlib 4.26 cannot construct it**: it has no Sobolev space and no
weak gradient (the only Sobolev file is
`Mathlib/Analysis/FunctionalSpaces/SobolevInequality.lean`, the
Gagliardo–Nirenberg–Sobolev inequality), so `H¹(ℝ^d)` and its closedness are not
available.  That is precisely why the existence of an energy measure for the
paper's form is carried as the external input
`SubdiffusiveProcess.DirichletForm.HasEnergyMeasure` rather than constructed: the input IS the
assertion of a nonzero witness.

A zero-form witness would also not, by itself, refute the emptiness argument  §0.1, which concerns nonzero forms.
That argument is defeated structurally instead, by restricting every calculus
field of `EnergyMeasure` to `D(E)`: with `locality`, `abs_cross_le` and
bilinearity available only on the domain, no step of the argument can be taken.

The witnesses over the **zero measure** (`m = 0`), where `L²(X, 0)` is trivial,
are used for the structures that require a core or an approximation property
(`IsCore`, `IsRegular`, `IsCoreAlgebra`, `IsKilledDomain`): over a general `(X, m)`
the zero form has no reason to be regular, since regularity is a statement about
`C_c(X)`, not about the form.
-/

open MeasureTheory Filter Topology

noncomputable section

namespace SubdiffusiveProcess.DirichletForm

variable {X : Type*} [MeasurableSpace X] [TopologicalSpace X]

/-! ## The zero form on an arbitrary `L²(X, m)` -/

                                                                       
                                                       
             
                      
                   
                          
                    
                                    
                                             
                                            
                                           
                
                
                                    
                               
                
                                                  
                                     
                            
                        
                       
                                                             
                                                           
                                     
                                                         
                                             
                          

                            
                                                                                               
                                      
                                          

                            
                                                                                                 
                     
                                        

                            
                                                                                             
                                    
                                                      

                                                                      
                                         
                                                                                                        
      

                                         
                                                                                        
                                  
                                                      

                            
                                                          
                                                                                             
                     
                                                  
                                                  

                                       
                                                                                      
                             
     

                                                   
                                                   
                                                  
                                       
     

                                                       
                                                     
                                                 
                                    

                            
                                                                                                         
                             
                                                        
                                                                   

                                                
                                                                              
                       
                       
                                           
                                    
                                     
                                      
                                               
                                              
                                      
                                            
                                          
                                         
                                                   
                                                         
                                                               
                         
                                                   

                                                                          
                                              

                                                                          
                                              

                                                         
                                                   
                                                                                
                                                            
                            
                                                  

                                                               
                                                        
                                                                                      
                  
                                 
                                   

                                                                    
                                            
                                                                           
                 
               
        
                       
           
                                               
        

                            
                                                          
                                                                                   
                     
                                                                                
         
                                           
      

                                  

                                                       
                                                                      
                       
                      
                           
                      
                                                
                                        
                               
                                

                            
                                                                     
                                                                                               
                       
                                                          
                   
                
                                                                
                           
                                                       
                           
                               

                                                                

instance instSubsingletonLpZero : Subsingleton (Lp ℝ 2 (0 : Measure X)) :=
  ⟨fun x y => Lp.ext_iff.2 (by rw [ae_zero]; exact Filter.eventually_bot)⟩

                            
                                                                                                
                                                 
                                   
                             

                            
                                                                                                
                                                
                                       

                                                                         
                                                        
                                                                                         
                                      
                   

                                                      
                                                                                        
                                                           
                   
                  
                                  
                                                                               
                    
                         
                                                            
                                                               

                                                                     
                                                          

                                                                     
                                                                                
                            
                                                                                         
                                                                                            
                                                    
                                                                 
                                                      
                                                                 

                                                                     
                              
                                                           
                                                  

                                                                            
       
                                        
                                                             
                     
                                               
              
                  
                                            
                                                                                  
                                                

                                                                  
                                      
                                                                                          
                                        
                               

end SubdiffusiveProcess.DirichletForm
