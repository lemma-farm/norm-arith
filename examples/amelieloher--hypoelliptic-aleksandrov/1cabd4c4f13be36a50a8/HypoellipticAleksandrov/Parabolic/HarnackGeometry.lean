module

public import HypoellipticAleksandrov.Parabolic.Geometry
public import HypoellipticAleksandrov.Measure.TimeVelocity
public import Mathlib.Topology.Constructions.SumProd
public import Mathlib.Topology.NhdsWithin
public import Mathlib.Topology.Order.DenselyOrdered

/-!
# Coordinate geometry for the parabolic Harnack argument

The Krylov--Safonov boxes in this file use coordinate cubes.  In particular,
they are not the metric balls inherited by `PDE.Vec d`.
-/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal

namespace HypoellipticAleksandrov.Parabolic

noncomputable section

/-- The open coordinate cube of radius `r` about `v₀`. -/
def velocityCube {d : ℕ} (v₀ : PDE.Vec d) (r : ℝ) : Set (PDE.Vec d) :=
  {v | ∀ i : Fin d, |v i - v₀ i| < r}

/-- The closed coordinate cube of radius `r` about `v₀`. -/
def velocityClosedCube {d : ℕ} (v₀ : PDE.Vec d) (r : ℝ) : Set (PDE.Vec d) :=
  {v | ∀ i : Fin d, |v i - v₀ i| ≤ r}

/-- The forward parabolic coordinate box of height `vartheta * r^2`. -/
def parabolicBox {d : ℕ} (vartheta r t₀ : ℝ) (v₀ : PDE.Vec d) :
    Set (TimeVelocity d) :=
  Ioo t₀ (t₀ + vartheta * r ^ 2) ×ˢ velocityCube v₀ r

                                                        
                                                                     
                           
                                                           

                                                                        
                                                                        
                           
                                                              

                                                                       
                                                       
                                                                    

                                                          
                                                    

                                                                          
                                                        
                                                      

                                                                     
def parabolicAffine {d : ℕ} (t₀ : ℝ) (v₀ : PDE.Vec d) (r : ℝ) :
    TimeVelocity d → TimeVelocity d :=
  fun z => (t₀ + r ^ 2 * z.1, v₀ + r • z.2)

                                                                         
                                                            
         

                                                                               
                                                                  
         

@[simp] theorem mem_parabolicBox_iff {d : ℕ} {vartheta r t₀ t : ℝ}
    {v₀ v : PDE.Vec d} :
    (t, v) ∈ parabolicBox vartheta r t₀ v₀ ↔
      t₀ < t ∧ t < t₀ + vartheta * r ^ 2 ∧ v ∈ velocityCube v₀ r := by
  constructor
  · rintro ⟨⟨ht₀, ht⟩, hv⟩
    exact ⟨ht₀, ht, hv⟩
  · rintro ⟨ht₀, ht, hv⟩
    exact ⟨⟨ht₀, ht⟩, hv⟩

                                                                        
                        
                                                  
                                                                            
             
                          
                       
                        
                         

                                                                           
                        
                                                     
                                                                               
             
                          
                       
                        
                         

                                                                           
                                
                                                                           
             
                          
                       
                        
                         

                                                                            
                                 
                                                           
     

                                                                                    
theorem velocityCube_eq_pi {d : ℕ} (v₀ : PDE.Vec d) (r : ℝ) :
    velocityCube v₀ r =
      Set.univ.pi fun i => Ioo (v₀ i - r) (v₀ i + r) := by
  ext v
  constructor
  · intro hv i _
    rw [mem_Ioo]
    rcases abs_lt.mp (hv i) with ⟨hleft, hright⟩
    constructor <;> linarith
  · intro hv i
    rcases hv i trivial with ⟨hleft, hright⟩
    exact abs_lt.mpr (by constructor <;> linarith)

                                                                                     
                                                                   
                             
                                                          
       
             
                
                
                                                
                            
              
                                            
                                                  

                                                                                            
                                                                    
                                                              
                                             
                                               
                                        
                      
                                                                      
         
                                                                   
                                                                   

                                                                            
theorem isOpen_velocityCube {d : ℕ} (v₀ : PDE.Vec d) (r : ℝ) :
    IsOpen (velocityCube v₀ r) := by
  rw [velocityCube_eq_pi]
  have hpi : Set.univ.pi (fun i : Fin d => Ioo (v₀ i - r) (v₀ i + r)) =
      ⋂ i ∈ (Finset.univ : Finset (Fin d)),
        (fun v : PDE.Vec d => v i) ⁻¹' Ioo (v₀ i - r) (v₀ i + r) := by
    ext v
    simp
  rw [hpi]
  exact isOpen_biInter_finset fun i _ =>
    isOpen_Ioo.preimage (continuous_apply i)

                                                                                
                                                                      
                                            
                               
                                                                       
                                                                                 
         
                   
                                                
               
                
                                 
                  
                
          
                                
                                              

                                            
                                                                     
                                        
                                          

                                              
                                                                           
                                              
                                                  

                                           
                                                                       
                                             
                               
                                                

                                         
theorem isOpen_parabolicBox {d : ℕ} (vartheta r t₀ : ℝ) (v₀ : PDE.Vec d) :
    IsOpen (parabolicBox vartheta r t₀ v₀) :=
  isOpen_Ioo.prod (isOpen_velocityCube v₀ r)

                                               
                                                                                 
                                                    
                                                          

                                          
                                                                                  
                                                     
                                                      

                                           
                                                                                   
                                                      
                                                        

                                              
                                                                                       
                                                          
                                                              

                                                      
                                                                                   
                                                      
                                            

                                                            
                                                                       
                      
                                                             
                                                          

                                                  
                                                                                               
                                                              

                                                        
                                                 
                                                               
                                          

                                                         
                                                  
                                                                
                                                                                      

                                                                                 
theorem volume_velocityCube_toReal {d : ℕ} {v₀ : PDE.Vec d} {r : ℝ} (hr : 0 ≤ r) :
    (volume (velocityCube v₀ r)).toReal = (2 * r) ^ d := by
  rw [velocityCube_eq_pi, Real.volume_pi_Ioo_toReal]
  · simp [Finset.prod_const, two_mul]
  · intro i
    linarith

                                                                       
                                                                         
                  
                                                                 
                               
                                                                  
           
            
                                                                       
                                                       
         
                   
                           
               
              
                                                                                    
                                 
                                
          
                                    
                                   

                                                                      
theorem volume_timeInterval_toReal (vartheta r t₀ : ℝ) (hvartheta : 0 ≤ vartheta) :
    (volume (Ioo t₀ (t₀ + vartheta * r ^ 2))).toReal = vartheta * r ^ 2 := by
  rw [Real.volume_Ioo, ENNReal.toReal_ofReal]
  · ring
  · nlinarith [mul_nonneg hvartheta (sq_nonneg r)]

/-- Product volume of a forward coordinate box. -/
theorem volume_parabolicBox_toReal {d : ℕ} {vartheta r t₀ : ℝ} {v₀ : PDE.Vec d}
    (hvartheta : 0 ≤ vartheta) (hr : 0 ≤ r) :
    (volume (parabolicBox vartheta r t₀ v₀)).toReal =
      (vartheta * r ^ 2) * (2 * r) ^ d := by
  rw [parabolicBox, Measure.volume_eq_prod]
  rw [MeasureTheory.Measure.prod_prod]
  rw [ENNReal.toReal_mul]
  rw [volume_timeInterval_toReal vartheta r t₀ hvartheta,
    volume_velocityCube_toReal hr]

                                                                                
                                                              
                                                                                  
                                                     
                                            
                                              
              
      

                                                                                     
theorem euclideanBall_subset_velocityCube {d : ℕ} {v₀ : PDE.Vec d} {r : ℝ}
    (hr : 0 < r) :
    PDE.euclideanBall v₀ r ⊆ velocityCube v₀ r := by
  intro v hv i
  have hcoord : (v i - v₀ i) ^ 2 < r ^ 2 := by
    simpa [PDE.euclideanSqDist, Pi.sub_apply] using
      (PDE.sq_apply_le_vecNormSq (v - v₀) i).trans_lt hv
  exact abs_lt_of_sq_lt_sq hcoord hr.le

                                                                                          
                                                                   
                                                                          
                                                  
                                 
                                                                       
                              
      
                                          
                             
                 
                       
                                                 
                                   
                                                              
                                         
                                        
                                    
                                               
                                       
                                                                           
                                                 

                                                                               
                                                             
                                                           
                                                                    
                                                
                                           
                                                
                                              
               
                
                     
                                                                                 
                                                            
                             
                                                                      
                     
                
                     
                                                                                 
                                                      
                                               
                                               
                                                 
                             
                              
                                              
                                      
                                                                         
                                   
             
                                                
                                     

                                                                              
                                                                       
                                   
                                                                      
                                           
            
                                                                 

                                                                
                                                                     
                                                                     
               
                                           
                              
                                 
                                   
             
                                  
         
                                                 
                                 
             
                                

                                                                                
                                                 

                                                                  
                                                

                                                                
                                                                                    
                           
                                                                                 
                                                       

                                                                  
                                                               
                                                                   
                                              
                                                                                            
           
            
      

                                                                         
                                                                            
                                                                   
                                              
                                                                                 
           
                                                 
      
                                                    
                                                             
                                                     
                                                       
            
                                             
                  
                                               
                                              
                 
                                          

end

end HypoellipticAleksandrov.Parabolic
