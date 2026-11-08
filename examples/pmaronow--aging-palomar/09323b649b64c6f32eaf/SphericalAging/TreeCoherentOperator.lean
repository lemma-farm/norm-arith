module

public import SphericalAging.TreeRootBlocks
public import SphericalAging.HilbertSchmidtTensor
public import Mathlib

public section

/-! The literal symmetric Hilbert--Schmidt operator of the coherent-root lemma.
Its norm and approximation estimate are transported through a canonical tensor
unit equivalence; its height blocks and self-adjointness hold as actual operators. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
open scoped InnerProductSpace TensorProduct Topology
open Set Filter
namespace SphericalAging.TreeCoherentOperator
open CausalTree CausalTree.HilbertDatum TreeCeilings TreeCoherentRoot TreeRootBlocks
local instance (α : Type) : DecidableEq α := Classical.decEq α

                                                                               
                                                                                                  
                                                                                       
                                          

                                                  
                                                                             
                                                                                              
                                          
                                                                                         
                                      
      

                                                                                                             
                              

                                                                                                         
                                      

                                                                       
                                                                            

                                                                        
                                                                

                                                   
                                        
                                                                       
                                                                              
                                            
                                  

                                                               
                                                                    
                                                                               
                                    
                                                                                 
                         
                                                                                        
                                                                    
                                                                                         
                                    
                                                
                                            

                                                                                         
                                                          
                                                                   
                                                                                                   
                        
         
                                                                   
                                                             
                                                                                 
      

                                                           
                                                                          
                  
           
                                                 
                                                
                
            
                                                                     
                
                             
                                                                            

                                                                            
                                                                     
                                                                       
                                                                              
                                                             
                      
                            
            
                            
            
                                                                                 
      

                                                                                              
                                                      
                                                                           
                                                   
                                                                                
                                                   
                                                                                
                                                                                           
                                                                                      
                                                    
                                           
                 
                                   

                                                                                               
                                                             
           
                                                                          
                                                 

                                                                            
                                                                              
                                                                                     
                                                           
                                                                             
                                                                                                
                                                                    
                                                               
                                                                         

end SphericalAging.TreeCoherentOperator
