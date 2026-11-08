/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.ClassReserveStage65.Ledger
public import PartitionedTriangleAbsorption.ClassCertificateLocalStage67
public import PartitionedTriangleAbsorption.SparseReserveGeometry

/-! # Structural hinge supply after physical edge deletion

All hinge counts refer to actual seven-edge sets, not projected type vectors.
Original root triangles may use deleted edges; a downstream consumer must supply
its own surviving root triangles. No universal common-neighbour query is used.
-/

@[expose] public section

namespace PartitionedTriangleAbsorption.ClassHingeDeletionStage69

open Finset ClassReserveStage65 ClassAwareHingesStage64 PhysicalHingeSupply
  SignedHinge BernoulliBlocks ClassCertificate TypedApplicationLinks
  ClassRepresentativesStage65 SparseReserveGeometry

variable {V : Type*} [Fintype V] [DecidableEq V]

                 
                                                    
                                            
                                           
                                                                   
                                                 
                                                         
                                                     
                                               
                                                
                                                         
                                                                              
                                                    
                                                                                  
           
                                     
                                                                       
                                                      
                                                            
                                                     
                                                                         
                                                                       
              
                                                                       
                                                                            
                                
                                                               
              
                                         
                                   
                                           
                                                   
              
                                                                          
                                       
                                                                               
                         
                                                                      
                                            
                        
                                                                                  
                                  
                                                                       
                                                
                                                               
                                                                 
                                                                                        
         
                                                                              
                         
                                            
                                                                                 
                          
                       
          

                       
                                                                
                                                                
                                                                             
                                         
           
                                   
                                                                              
                       
            
                                                                       
                           
                                                   
                                                    
              
                                   
                                                                                  
                                                                              
                                                             

                 
                                                    
                                            
                                           
                                                                   
                                                         
             
                                                                   
                                                           
                                              
                                                          
           
                      
                                                      
                                                      
                                                                                       
                                                                                
                                                                               
                                                                                   
                                        
                                                                             
                                                                             
                                             
                                                         
                                                       
                                                 
                           
                                                     
                                                                            
                                                      
                                                     
                                                         
                                                  
                           
          
                                   
                                  
              
                                            
                                                       
              
                                      
                                    
                                                                                       
                                                              
                                                     

end PartitionedTriangleAbsorption.ClassHingeDeletionStage69
