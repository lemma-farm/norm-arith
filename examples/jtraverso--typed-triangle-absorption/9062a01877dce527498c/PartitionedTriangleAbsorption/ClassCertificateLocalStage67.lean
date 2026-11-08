/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.ClassCertificate.Producer
public import PartitionedTriangleAbsorption.ClassRepresentativesStage65

/-! # Local physical certificates after bounded edge deletion

The certificate uses only source edges, source-to-representative edges and the
representative tetrahedron. Missing edges elsewhere in the host are irrelevant.
Structural F3 divisibility remains an explicit hypothesis, not coarse F0 divisibility.
-/

@[expose] public section

namespace PartitionedTriangleAbsorption.ClassCertificateLocalStage67

open Finset TypedApplicationLinks SignedCertificate IntegerCertificate
open ClassCertificate ClassLatticeStage65 LocalCycleTransportStage62 ParityBalanceStage63

universe u
variable {V : Type u} [Fintype V] [DecidableEq V]
variable {cls : V → Fin 4} {G : SimpleGraph V} {r : Fin 4 → V}

                                                                 
                                                               
                                                                    
                                                                   

                                            
                                                      
                                             
                                         
                                           
                                                         
                                                   
                                
                                                                              
                                                                      
                                                                                        
                                                               
                                
                                                                                       
                                                          
                                                          
                                                                                      
                                                         
                                                          
                                               
          
                                                                           
                     
                         
                                                                              
                                        
                     
      

                                                 
                                                    
                                                       
                                                     
                                                                
                                                                      
                                                                               
                                                               
                             
                                                                                   
                                                                             
                             
                             
          
                                                                                  
                                                             
          
      

theorem degVec_zero_outside {P : Finset (Sym2 V)} {v : V} (hv : v ∉ vertSet P)
    (j : Fin 4) : degVec cls P v j = 0 := by
  simp only [degVec, Finset.sum_apply]
  refine sum_eq_zero fun e he => ?_
  have hve : v ∉ e := by
    intro h
    exact hv (mem_filter.mpr ⟨mem_univ v, e, he, h⟩)
  induction e using Sym2.ind with
  | _ a b =>
    have ha : a ≠ v := by intro h; subst a; exact hve (by simp)
    have hb : b ≠ v := by intro h; subst b; exact hve (by simp)
    simp [degContrib_mk, ha, hb]

                                            
                                                                  
                                                                        
                                                                      
                                                                               
                             
                                                
                                                            
                                                  
                                                               
                         
                                        
                                                         
                                                         
                                                         
                                                                   
                                              
                                                                   
                                              
                                                                   
                                              
                                                      
                                                                      
                                                   
               
                                                                          
              
                                               
                                                   

                                                
                                                                  
                                                                          
                                                                      
                                                                         
                               
                                     
                                                                    
                                    
                                      
                                   
                  
                                                                          
                                                                             
                                       
                                                             
                                                       
                                                                            
                        
                                                                                  
                                                                     
                                 
                                                                                  
                                                                     
                                 
                                                                                  
                                                                     
                                 
                                                                                  
                                                                     
                                 
                                                                  
             
            
                                                                                    
                  
        
                                    
                       
            

                                                                                     
                                                                                 
                                                                  
                                                                      
                              
                                                              
                                                       
                                                                     
                                   
              
                                                                                  
                                                                                  
                                                                                  
                               
                                                                                   
                                               
                                          
                                                                           
                                                           
         
     

                                                                                 
                                                                                             
                                                    
                                                                     
                                                                  
                                                                                
                                                  
                                                                        
                                                                                      
                                                    
                                                       
                                                                                     
                                                      
                                                                                       

                                                                            
                                                           
                                                                     
                                                             
                        
                                                                                
                                                                             
                                                                                      
                                                    
                                                                  
                                                                      
                                      
                                                   
                                      
                                                 
                                                                     
                                 
                                                                                                
                                  
         
                       
                 
                                                                      
                  
                                                               
                              
                                                                             

end PartitionedTriangleAbsorption.ClassCertificateLocalStage67
