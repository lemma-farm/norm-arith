/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.BlowupB.Defs
public import PartitionedTriangleAbsorption.PhysicalHingeSupply.Consumer

/-! # From a bounded physical certificate to an F0 absorber

The support bounds hold for every family of partitioned triangles. Only the last two
theorems specialize to F0 and use the existing common-neighbour/physical-hinge producer.
They require a bound on physical certificate cost and common-neighbour richness of
order four. They do not establish the general candidate for Theorem 13.16 or [17].
-/

@[expose] public section

namespace PartitionedTriangleAbsorption.PhysicalCertificateProducer

open Finset BlowupB SignedCertificate SignedHinge TypedApplicationLinks

variable {V : Type*} [Fintype V] [DecidableEq V] {t : ℕ}
  {p : V → Fin t} {F : Finset (Multiset (Fin t))} {G : SimpleGraph V}
  {ι : Type*} [Fintype ι] {P : Finset (Sym2 V)} {T : ι → Finset V} {c : ι → ℤ}

                   
                                                                                   
                                                                        
                                                          
                                                            
                             
            
                                                         
                                             
              
                               

                                                                                 
                                                               
                                                                        
           
            
                                          
                                                      
                                            
                      
                                                   

                                                                                        
                                                                
                                                 
           
                                                             
        
                        
                                                                      
                                                   
                                                                   
                                     
                                       
                             
                   
                                                 
                                                               
               
                                                       
                                                                         
                        
                   

                                                                                       
                                                                                 
                          
            
                                                     
                                 
            
                                          
                                                           
                                                            
                                  
                                                                       

                                                                         
                                                                            
                                  
                                  
                                                                                    
                                
                      

end PartitionedTriangleAbsorption.PhysicalCertificateProducer

namespace PartitionedTriangleAbsorption.PhysicalCertificateProducer

open Finset BlowupB SignedCertificate SignedHinge TypedApplicationLinks PhysicalHingeSupply
  F0Geometric

                                                                                      
                                                                          
                                                                  
                                                                                        
                                                              
                                                       
                                                         
                                                                
                                   
                                                                  
                                                                                     
                                         
                                                                           
                                                                   
                                                    
                                                                                     
                                                 
                                              
                                   
                                                                     
                                                                   

                                                                                        
                                                                  
                                                              
                                                                             
                                                                 
                                                                                 
                                                                        
                                                        
                                               
                                                                                 
                                                                                
                                                                              
                                                                                           
                                                       
                                                             
                   
                              
                                              
                                   
                                             
                                                     

end PartitionedTriangleAbsorption.PhysicalCertificateProducer
