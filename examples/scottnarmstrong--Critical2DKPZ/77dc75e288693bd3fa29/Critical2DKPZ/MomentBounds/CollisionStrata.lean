/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.Definitions.Site
public import Critical2DKPZ.SHF.DeltaBose.CollisionWords
public import Mathlib
import Mathlib.Data.Fintype.Basic
import Mathlib.Tactic

/-!
# Replica partitions and the two collision-stratum conventions

A partition is its equivalence relation on the finite label set. LZ21 imposes
only equality inside blocks. CCR25 additionally separates distinct nonsingleton
blocks, while allowing singleton labels to coincide with all other coordinates.
-/

@[expose] public section

noncomputable section

namespace Critical2DKPZ.MomentBounds

/-- A partition of the replica labels, represented by its equivalence relation. -/
abbrev ReplicaPartition (h : ℕ) := Setoid (Fin h)

                                             
                                                   

                                               
                                                                           
                              

                                                                                    
                                                                                                   
                            

                                                                                       
                                                                                                    
                                      
                                                                      



                                                                               
                                                                                                          
                                                                            
                                
                                                                                   
                     
                               
                 
                               
                        
                                  

                                                                                                   
                                                                                 
                                     
                                                                          

                                                                   
                                                                       
                                                                          

                                                                                                  
                                                                                
                                  
                                                                             
             
            
                                          
                    
                                  
         
                                                         
         
              
                   
         



end Critical2DKPZ.MomentBounds
