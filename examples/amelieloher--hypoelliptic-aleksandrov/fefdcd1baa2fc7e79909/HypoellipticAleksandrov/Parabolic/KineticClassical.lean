module

public import Mathlib.Analysis.Calculus.ContDiff.FiniteDimension
public import HypoellipticAleksandrov.Ambient.MatrixContraction
public import HypoellipticAleksandrov.Coefficients.Ellipticity
public import HypoellipticAleksandrov.Geometry.KineticPoint
public import PDEFoundation.Sobolev.ClassicalGradient

/-!
# Classical kinetic product API

This module fixes the product-cylinder geometry, anisotropic classical
regularity, and plus-sign kinetic operator used in the time-velocity estimates.  The kinetic points
retain their explicit time, position, and velocity fields; product sets are transported only through
`KineticPoint.homeomorphProd`.

No maximum theorem is proved here.
-/

@[expose] public section

noncomputable section

namespace HypoellipticAleksandrov.Parabolic

                                                                
                                                                              
                           
                                                                   

                                                                                  
                                                                                
                           
                                     
                                                 

                                                            
                                                                           
                           
                                     
                                                  

                                                                        
                                                                                    
                           
                                     
                                                  

                                                                         
                                                                                     
                           
                                     
                                                  

                                                                                       
                                                             
                                                       
                                        
                                                   
                                                   

                                                      
                                                                      
                                                    
                                                
                                                                         
                                                                             
             
                               
                            
                             
                              

                                                       
                                                                        
                                                    
                                                  
                                                                                         
                                             
                                                   
             
                               
                            
                             
                              

                                                                     
                                                                   
                                                    
                                             
                                                                           
                                             
                                                    
     

                                                                            
                                                                            
                                                    
                                                      
                                                                                          
                                             
                                                    
             
                               
                            
                             
                              

                                                                             
                                                                             
                                                    
                                                       
                                                                                          
                                             
                                                    
             
                               
                            
                             
                              

                                                                                     
                                                                                 
                                                    
                                                           
                                                                         
                                                               
                                    
                                                              
                                         
                                                                  
                                                                                 
                                                        

                                                                 
def kineticTimeDerivative {d : ℕ} (u : KineticPoint d → ℝ) (z : KineticPoint d) : ℝ :=
  deriv (fun r => u ⟨r, z.position, z.velocity⟩) z.time

/-- The position gradient with time and velocity held fixed. -/
def kineticPositionGradient {d : ℕ} (u : KineticPoint d → ℝ) (z : KineticPoint d) :
    PDE.Vec d :=
  PDE.classicalGradient (fun x => u ⟨z.time, x, z.velocity⟩) z.position

/-- The velocity gradient with time and position held fixed. -/
def kineticVelocityGradient {d : ℕ} (u : KineticPoint d → ℝ) (z : KineticPoint d) :
    PDE.Vec d :=
  PDE.classicalGradient (fun v => u ⟨z.time, z.position, v⟩) z.velocity

/-- The velocity Hessian indexed as `D_i(D_j u)`. -/
def kineticVelocityHessian {d : ℕ} (u : KineticPoint d → ℝ) (z : KineticPoint d) :
    PDE.Mat d :=
  fun i j =>
    (fderiv ℝ (fun v : PDE.Vec d =>
      PDE.classicalGradient (fun w : PDE.Vec d => u ⟨z.time, z.position, w⟩) v)
      z.velocity (PDE.basisVec i)) j

/--
The anisotropic kinetic `C^{1,1,2}` regularity predicate. It asks only for
one time, one position, and two velocity derivatives on separate slices.
-/
def IsKineticC112On {d : ℕ} (u : KineticPoint d → ℝ) (D : Set (KineticPoint d)) : Prop :=
  ContinuousOn u D ∧
    (∀ z ∈ D, DifferentiableAt ℝ (fun r => u ⟨r, z.position, z.velocity⟩) z.time) ∧
    (∀ z ∈ D, ContDiffAt ℝ 1 (fun x => u ⟨z.time, x, z.velocity⟩) z.position) ∧
    (∀ z ∈ D, ContDiffAt ℝ 2 (fun v => u ⟨z.time, z.position, v⟩) z.velocity) ∧
    ContinuousOn (kineticTimeDerivative u) D ∧
    ContinuousOn (kineticPositionGradient u) D ∧
    ContinuousOn (kineticVelocityGradient u) D ∧
    ContinuousOn (kineticVelocityHessian u) D

namespace IsKineticC112On

                                                              
                                                                                
                                                   
     

                                                                                
                                                                   
                                                                             
                  
                                                                         
            

                                                                      
                                                                 
                                                                             
                  
                                                                     
              

                                                                      
                                                                 
                                                                             
                  
                                                                     
                

                                                                      
                                                                           
                                                          
                                               
             

                                                                        
                                                                             
                                                          
                                                 
               

                                                                        
                                                                             
                                                          
                                                 
                 

                                                                       
                                                                            
                                                          
                                                
                 

                                                                                  
                                                             
                                                                             
                  
                                                                                   
                  
                                                    

end IsKineticC112On

                                                                      
                                                                                    
                               
                             
                                                         
                                                                          

                                                            
                                                                             
                                                   
                                  
                                 
                                                             
                                                                                 
     

end HypoellipticAleksandrov.Parabolic
