/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.BlowupB.Families
public import Mathlib.Tactic.Linarith
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Data.Int.Interval

/-! # BlowupB.Cost — ℓ¹ norms, entry bounds, bounded lattice representations

* `l1 w = ∑ e, |w e|`, subadditive, homogeneous; `l1 (indZ E) = |E|`; a certificate of cost `K`
  has `l1 ≤ 3K` (`l1_le_of_physCostZ`);
* the entries of edge-count and degree vectors are bounded by `2 · l1`
  (`abs_edgeVecZ_le`, `sum_abs_degVecZ_le`);
* `exists_rep_bound`: on a finite set of lattice vectors (a box) representations of bounded
  cost can be chosen uniformly. With `boxVec`, `boxMat` this gives constants depending only on the
  family and on the size bound, never on the host.
-/

@[expose] public section

namespace PartitionedTriangleAbsorption.BlowupB

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V] {t : ℕ}

/-! ### ℓ¹ norm -/

                                               
                                         

                       
                                                                                   

                       
                                                         

                       
                                                                           
           
                        
                                            

                       
                                                                

                                                                           
                                                       

                       
                                                                        
                                                              

                                                                   
                                               
           
                                            
                           
                       
                                     
                                                      

                                                                  
                
                                                                                        
                      
             
                                                               

                   
                                                                                       
                                                                    
                                 
                     

                                                                                          
              
                                    

                                                          
                                                                                              
                                                                           
                                         
                                                       
            
                               
                                                                     
          
                                                                                       
                     
                                                                                       
                                               
                                                                                  
                                                                                      
                            

                       

omit [Fintype V] [DecidableEq V] in
theorem pairVec_nonneg (p : V → Fin t) (e : Sym2 V) (i j : Fin t) : 0 ≤ pairVec p e i j := by
  induction e using Sym2.ind with
  | _ a b => simp only [pairVec, Sym2.lift_mk]; split_ifs <;> norm_num

                                   
                                                                                             
                                 
                                                                      

omit [Fintype V] in
theorem degContrib_nonneg (p : V → Fin t) (v : V) (e : Sym2 V) (j : Fin t) :
    0 ≤ degContrib p v e j := by
  induction e using Sym2.ind with
  | _ a b => simp only [degContrib, Sym2.lift_mk]; split_ifs <;> norm_num

                                                                                    
                                     
                                                              
                                                                
                  

                                                         
                                          
                                 
            
                                                         
                                                       
            

                       
                                                                        
                                       
                     
                                                                                            
                                                  
                                                            
                                                                               
                                                                                    

                                                             
                                                
                                                                                    
           
                                                                            
                                         
                            
                                                                                        
                                                                 
                                                    
                                                                       
                                                                                 
                                  
                                                       
                                                                     
                      
                                    
                        
                                                   

                                                                             
                                      
                                                         
                                                                                          
                                                                   
                                                        
                                                                  
                                                    

                   
                                                                                        
                              
                                 
            
                                                                             
                                                                              
            
                             

                                                                          
                                                        
              
                                       
         
                
                                  
                        
                       
                                                              

                                                                                    
                                        
                                          
                                                                                             

                                                 

                 
                                                                            
                                                                                   
                              
                                                                              

                                                                                            
                                     
                
           
                                            
                   

                                                                                                
                                                                               
                                                                                              
                                                                                      
                                                                    
           
                                                                             
                                                
                                                        
                                  
            
                                                          

                                                            
                                                                                              

                                                                                        
                                                                  

                                                             
                                                                                             

                                                            
                                           
                                                      

end PartitionedTriangleAbsorption.BlowupB
