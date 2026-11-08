module

public import PDEFoundation.Sobolev.H1.Graph
public import PDEFoundation.Sobolev.W1p.ZeroBoundary
public import Mathlib
/-!
# Zero-boundary `H¹` graph

This file is the `p = 2` facade for the canonical zero-boundary graph from
`PDEFoundation.Sobolev.W1p.ZeroBoundary`.  In particular, `H10Graph hU` is
definitionally the closure in `H1Graph U` of the range of actual bundled
smooth compactly supported test functions.  No second weak-gradient relation
or boundary-condition predicate is introduced here.

For compatibility with `LeanIntoHomogenization`, the file also exposes its
representative-level `H10Function` field surface.  That structure merely
bundles an `H1Function` with the same supported smooth approximation
certificate used to enter the closed graph.

## Main definitions

- `H10Function`: the LIH-compatible representative facade.
- `MemH10`: concrete-function membership through that facade.
- `h10GraphClosedSubmodule`: the closed `H¹₀` submodule of `H1Graph U`.
- `H10Graph`: its complete carrier.
- `H1Function.SupportedSmoothApproximation`: the exact representative-level
  `p = 2` specialization of the generic certificate.

## Main results

- `H1Function.mem_h10Graph_of_supportedSmoothApproximation` sends an explicit
  supported approximation to the complete carrier.
- `H10Graph.exists_tendsto_smooth` supplies actual bundled test functions
  converging to every point of the complete carrier.
-/

@[expose] public section

open scoped ENNReal Topology

namespace PDE

open Filter

variable {d : ℕ} {U : Set (Vec d)}

/-- A representative-level `H¹₀(U)` witness with the exact field surface used
by `LeanIntoHomogenization`.

The additional fields are precisely a supported smooth approximation
certificate for `toH1Function`; they do not define a second boundary
condition. -/
structure H10Function {d : ℕ} (U : Set (Vec d)) extends H1Function U where
  approx : ℕ → Vec d → ℝ
  approx_smooth : ∀ n, ContDiff ℝ (⊤ : ℕ∞) (approx n)
  approx_hasCompactSupport : ∀ n, HasCompactSupport (approx n)
  approx_support_subset : ∀ n, tsupport (approx n) ⊆ U
  tendsto_approx :
    Filter.Tendsto
      (fun n =>
        MeasureTheory.eLpNorm
          (fun x => approx n x - toH1Function.toFun x)
          (2 : ℝ≥0∞) (MeasureTheory.volume.restrict U))
      Filter.atTop (nhds 0)
  tendsto_approx_grad :
    ∀ i : Fin d,
      Filter.Tendsto
        (fun n =>
          MeasureTheory.eLpNorm
            (fun x =>
              (fderiv ℝ (approx n) x) (basisVec i) -
                toH1Function.grad x i)
            (2 : ℝ≥0∞) (MeasureTheory.volume.restrict U))
        Filter.atTop (nhds 0)

instance : CoeFun (H10Function U) (fun _ => Vec d → ℝ) where
  coe u := u.toH1Function.toFun

                                                                       
                                                                       
                                                              
                                               

                                                                          
                                                            
                                                              
                                    
                                               

                                                              
noncomputable abbrev H10Graph (hU : IsOpen U) :=
  W10pGraph (p := (2 : ℝ≥0∞)) hU

                                                                         
                           
                                                                    
                                           
                                                         

                                                                     
                            
                                                                               
                              
                                                                

                                                                  
                            
                                                    
                                              
                                          
                                                 
                                                                       

                                                                  
              
                                                              
                                                             
                                                                    

namespace H1Function

variable {u : H1Function U}

/-- Explicit supported smooth approximation data for an `H1Function`,
definitionally the generic `W¹,2` certificate. -/
abbrev SupportedSmoothApproximation (u : H1Function U) : Type :=
  W1pFunction.SupportedSmoothApproximation u.toW1pFunction

                                                              
                
                                                                   
                                                             

                                                                           
                                                                         
               
                                    
                                                                    
                   
                          
                                        
                                                              
                                                         
                                         
                                             

       
                                                     
                                                
                                                 
     

                                                              
                                         
                                                                 
                                                
                       
                                

                                                                 
                                         
                                                                    
                                                   
                          
                               
                                                        

                                                                           
                                            
                                                                    
                                                                              
                                                                       

                                                                     
                                              
                                                      
                                                                
           
                                                  
                                       
                                             
                               

                                                                        
                                                       
                                                    
                                      
                                                
                                                                            
                                                                          

                                                                   
                                                      
                                                       
                                      
                                                   
                                                                            
                                                                             

end H1Function

namespace H10Function

variable {u : H10Function U}

@[ext]
theorem ext {u v : H10Function U}
    (htoH1Function : u.toH1Function = v.toH1Function)
    (happrox : u.approx = v.approx) : u = v := by
  cases u
  cases v
  cases htoH1Function
  cases happrox
  rfl

                                                          
                                   
                                   
                      

                                                                 
                                  
                                    
                                    
          

                                                                              
                 
                                                      
                                                     
                    
                                  
                                                        
                                                   
                                   
                                       

                                                                        
                                              
                                                             
                                                     
                                  

       
                                                                        
                                                                         
         
     

                                                                             
                                            
                                                                     
                         
                                                     

       
                                                              
                                                  
     

                                                                        
                             
                                                               
           
               
                                                                    
                                                          
                                                     

                                                                            
                                             
                                                          
                                             
                                                 
                                                             
                                     

                                                                             
         
                                                                  
                  
                                                              

       
                                                            
                                   
                                                
     

                                                                
                                               

                                                                    
                                                                       
                                
noncomputable def ofContDiff (hU : IsOpen U)
    {f : Vec d → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (hcompact : HasCompactSupport f) (hsub : tsupport f ⊆ U) :
    H10Function U where
  toH1Function :=
    (W1pFunction.ofContDiff hU (hf.of_le (by simp)) hcompact
      (2 : ℝ≥0∞)).toH1Function
  approx := fun _ => f
  approx_smooth := fun _ => hf
  approx_hasCompactSupport := fun _ => hcompact
  approx_support_subset := fun _ => hsub
  tendsto_approx := by
    simpa only [W1pFunction.ofContDiff, W1pFunction.toH1Function_toFun,
      sub_self, MeasureTheory.eLpNorm_fun_zero] using
      (tendsto_const_nhds :
        Tendsto (fun _ : ℕ => (0 : ℝ≥0∞)) atTop (𝓝 0))
  tendsto_approx_grad := by
    intro i
    simpa only [W1pFunction.ofContDiff, W1pFunction.toH1Function_grad,
      sub_self, MeasureTheory.eLpNorm_fun_zero] using
      (tendsto_const_nhds :
        Tendsto (fun _ : ℕ => (0 : ℝ≥0∞)) atTop (𝓝 0))

       
                                        
                                                
                                                              
                                                              
     

       
                                       
                                                
                                                              
                                                        
                                               
     

       
                                         
                                                
                                                            
             
                                                    
     

end H10Function

namespace H1Function

       
                                                  
                                                                   
                                                                          
               
     

end H1Function

                                                                      
                                                          
                                                           
                   
                         
               

namespace H10Graph

                                                                       
                                 
                                                                      
                        
                                                                
                                              
                                                             

                                                                        
                                      
                                                                 
                                 
                                                                 
                                    
                                                        

end H10Graph

end PDE
