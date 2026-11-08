module

public import Mathlib

@[expose] public section

noncomputable section

namespace DedekindZetaZeroFree.KPContLocalNorm

open MeasureTheory Filter Topology TopologicalSpace

abbrev Space (n : ℕ) := EuclideanSpace ℝ (Fin n)

structure LocalBall (n : ℕ) where
  dimension_pos : 0 < n
  center : Space n
  radius : ℝ
  radius_pos : 0 < radius

def LocalBall.carrier {n : ℕ} (B : LocalBall n) : Set (Space n) :=
  Metric.ball B.center B.radius

def LocalBall.toOpens {n : ℕ} (B : LocalBall n) : Opens (Space n) :=
  ⟨B.carrier, Metric.isOpen_ball⟩

abbrev MultiIndex (n k : ℕ) :=
  {α : Fin n → Fin (k + 1) // (∑ i, (α i).val) ≤ k}

def MultiIndex.degree {n k : ℕ} (α : MultiIndex n k) : ℕ :=
  ∑ i, (α.val i).val

def MultiIndex.directions {n k : ℕ} (α : MultiIndex n k) : List (Fin n) :=
  (List.finRange n).flatMap (fun i => List.replicate (α.val i).val i)

def coordinateDerivativeList {n : ℕ} : List (Fin n) → (Space n → ℂ) →
    (Space n → ℂ)
  | [], u => u
  | i :: is, u => fun x =>
      fderiv ℝ (coordinateDerivativeList is u) x (EuclideanSpace.single i 1)

def coordinateDerivative {n k : ℕ} (α : MultiIndex n k)
    (u : Space n → ℂ) : Space n → ℂ :=
  coordinateDerivativeList α.directions u

abbrev BallL2 {n : ℕ} (B : LocalBall n) :=
  Lp ℂ 2 (volume.restrict B.carrier)

def IsWeakDerivative {n k : ℕ} (B : LocalBall n) (α : MultiIndex n k)
    (u v : BallL2 B) : Prop :=
  ∀ φ : TestFunction B.toOpens ℂ ⊤,
    (∫ x in B.carrier, u x * coordinateDerivative α (fun y => φ y) x) =
      (-1 : ℂ) ^ α.degree * (∫ x in B.carrier, v x * φ x)

structure IntegerSobolev {n : ℕ} (B : LocalBall n) (k : ℕ) where
  derivatives : MultiIndex n k → BallL2 B
  weak_derivatives : ∀ α : MultiIndex n k,
    IsWeakDerivative B α (derivatives (⟨fun _ => 0, by simp⟩ : MultiIndex n k))
      (derivatives α)

                                                           
                                   
                                             

                                                                
                                   
                    

                                                                       
                                                                 
                                                               

                                                         
                                                        
                       
                           
                                                             
                       
                              
                            
           
                                                 
                                        

                                                     
                                                              
                                                                                             
                  
                   
                   
                                                                                       

                                                            
                                                     
                                                            
                  
                   
                   
                                                              

                                                                           
                                                              
                  
                               
                   
                                                     

                                                                     
                                                                               
                                                       
                                                                
            
                                                                               
                                                                             
                                                                          
                                                                                      
                                                                                     
                                   
                                             
                                               

                                                                     
                                                                                  
                                                                                          
                  
                          
                  
              
                                                                                  
                                                                
                                                                                   
                                              
                                           

                                                                                        
                                                                                  
                                                                                
                                              
                                                                             
                                          
                                                      

                                                                       
                                            
                                                           
                                               
                                                                
                                                                       
                                                                  
                       
                                                                     
                                 
                                                               
                                                                        
                                                                                                
                                                                                                       
                                                                          
                                                                                                  
                                                               
                                                                        
                                                       
                                                         
              
                                                                       
             
                                                                        
                                                       
                                                         
              
                                                                      
             
             
         

                                                                            
                                         
                                                                     
                  
              
                                                                             

                                                                      
                                            
                                                           
                                                      
                                                              
                                                                                          
                                 
                                          
                  
                                                                   
                                                                    
                                            
                                                              
                                             
                                                                                                      
                                          
                                                                                     
                                                             
                        
                                                                    
                                                                                                         
                                                                           
                                                                  
                
                                                    
                                         
        

                                                                  
                                        
                                                                      
                                      

                                                                  
                                                              
                                
                                                                       
                             
                           
                                                                       
                                                                                       
                                 
                                                                                   
             
                                                                                          
                                                                                         
               
                        
                    
                                       
                                                                                        
                                                                                                           
                                                                                           
                                                                                        
                        
                                                                               
                                                  
                                                                             
                             
                                   
             
                                               
                                                                
                             
                                   
             
               
                                                              
                                                                                                  
                               

                                                         
                                    

                                                                  
                                                              
                                                                                             
                  
                   
                   
                                                                                       

                                                              
                                          
                                                                    
         
                                             
                                                                                          

                                                                     
                                   
                                                                 
           

                                                                            
                                                                   
                                                   
                                                       

                                                                  
                                                             
                                                    
                                                                   
                                                      
                                                      
                                                     
                                      
                                 
                                                                                        

                                                            
                                               
                                                   
                                                                 

end DedekindZetaZeroFree.KPContLocalNorm

end
