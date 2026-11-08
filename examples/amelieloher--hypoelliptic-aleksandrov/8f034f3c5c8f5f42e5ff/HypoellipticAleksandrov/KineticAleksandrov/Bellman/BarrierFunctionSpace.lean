module

public import HypoellipticAleksandrov.KineticAleksandrov.Bellman.BarrierFunctionSpaceGeometry
public import Mathlib.Topology.ContinuousMap.Compact
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Tactic

/-! # C² homogeneous functions and their continuous Bellman images -/

@[expose] public section
noncomputable section
open Set Filter Topology
namespace HypoellipticAleksandrov.KineticAleksandrov

                                        
                                                         

                                                                                  
                                                                  
                                          
                                               
                                                        

                                           
                                                    
                       

                                           
def bellmanDv (phi : (ℝ × ℝ) → ℝ) (q : ℝ × ℝ) : ℝ :=
  fderiv ℝ phi q (0, 1)

/-- The second velocity derivative. -/
def bellmanDvv (phi : (ℝ × ℝ) → ℝ) (q : ℝ × ℝ) : ℝ :=
  fderiv ℝ (bellmanDv phi) q (0, 1)

                                                                     
                                                                  
                                              

                                     
                                                                                
                                

                                                                               
                                                               
                                                                          
                                                                        
                                                                                 
                    

                                                          
                                                        
                                                              
                                                       
                                                

                                                                   
                                                         
                                                              
                                                           
                                                           
                                                                             
                      

                                                                                   
                                                                 
                                                              
                                                                     
                                                
                                                                                         
                                              
                                                                                  
                                                        
                                                      
                                                       
                                                                    
                                                                                

                                                           
                                                              
                                                                                              
                                                                    

                                                                                    
                                                                         
                                                   
                 
                                 
                   
                                       
                
                           
                                  
                   
                                                                         
                 
                    
                                             
                   
                                                            
        

end HypoellipticAleksandrov.KineticAleksandrov
