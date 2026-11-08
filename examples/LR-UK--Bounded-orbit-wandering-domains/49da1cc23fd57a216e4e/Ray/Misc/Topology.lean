module
public import Mathlib.Analysis.Normed.Group.Basic
public import Mathlib.Topology.Connected.LocallyConnected
public import Mathlib.Topology.Defs.Basic
public import Mathlib.Topology.Defs.Filter
public import Mathlib.Topology.MetricSpace.Defs
public import Mathlib.Topology.MetricSpace.ProperSpace
public import Mathlib.Topology.Order.Real
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Basic.Complex.Basic
import Mathlib.Basic.Real.Basic
import Mathlib.Data.Set.Basic
import Mathlib.Topology.MetricSpace.Basic

/-!
## Various topology lemmas
-/

open Classical
open Metric (ball closedBall sphere mem_sphere mem_ball)
open Filter
open OrderDual (ofDual toDual)
open Set
open scoped Real NNReal Topology Filter ENNReal
noncomputable section

                                                                     
                                                                                                  
                                                                                                   
                                                                          
                                                                                              
                                                                   
                                                                                              
                                                                         
                                         
                                               
                                                             
                                                       
                                         
                       
                                                                                             
                
                       
                                                     
                                                                              
                                                                   
                
                                        
                                                     
                                                                     
                            
                                                                        
                                                        
                                               
                                                   
                                  

                                               
                                                                                         
                                                                         
                                        

                                                   
                                                                                           
                                                                             
                                        

                                              
                                                                        
                                                     
                                                                 
                                        
                                   
                               

                                                                                  
                                                                                
                                                                                                    
                           
                                                                                         

                                                                              
                                                                 
                                                                                                  
                                                                    
                                                                    
                                    
                                                 
                                                      
                                                                              
                                                                                     
                                                          
                                                                      
               
                                                                                               
                                                                                       
                                     
                                                                 
                      
                                                                    
                                                                               
                                  
                    
                                                                     
                                                                                             
                 
                   

                                                                                              
                                                       
                                                       
                                                                               
                               
                                                         
                                          
                                          
                                    
                                                          
                                                                    
                                      
                                    
              
              
                                                                       
                                                        

                                                                                                
                                                     
                                                             
                                                                                       
                                   
                                                                                        
                                  
                                

                                                                                  
                             
                                                                         
                                                                                          
                                                          
                                              
                                                                            
                                                            
                                                                              
                                 
                                                                 
                                                                 
                                                       
                                                                                  
                                                        

                                                                               
                          
                                                                                         
                                                        
                                                    
                                                                  
                                       

              
                                                                                               
             
                                                                                        
                    
                                                                                     
                                                                                           
     

                                                                    
public theorem MapClusterPt.prod {A B C : Type} [TopologicalSpace B] [TopologicalSpace C]
    {f : A → B} {g : A → C} {a : Filter A} {b : B} {c : C}
    (fa : MapClusterPt b a f) (ga : Tendsto g a (𝓝 c)) :
    MapClusterPt (b, c) a fun x ↦ (f x, g x) := by
  rw [mapClusterPt_iff_frequently] at fa ⊢; intro s n
  rcases mem_nhds_prod_iff.mp n with ⟨u, un, v, vn, sub⟩
  apply (fa _ un).mp
  apply (Filter.tendsto_iff_forall_eventually_mem.mp ga v vn).mp
  exact .of_forall fun x gv fu ↦ sub (mk_mem_prod fu gv)

                                                                                  
                                                                                       
                                                                                
                                           
                                                  

                       
                                                                                                   
                                          
                                                          

                                        
                                                                                              
                                    

                                                                                           
                                                                                             
                                                
                                   

                                                           
                                                                                           
                                                                     
                                                                    
                                                                                   

                                                                                         
                                                                                  
                                                                      
                                                       
                                                           

                                                                                       
                                                                                                
                                                                                       
                                           
                                   
                                                                            
                                          
                                                                                          
                                                                             
                                                              
                           
                 
                              
             
                                                 
             
                
                                                                                     
                         
                                        
            

                                   
                                                                                              
                                                                  
                                                                                          
             
                  
                                                            
                  
                                                
                                                  
            

                                                    
                                                                                                    
                                                                        
                                                                                                
             
                  
                                                            
                  
                                                
                                                        
            

                                               
                                                                                                    
                                                                          
                                                   
                                                       
                      
                                              
                                                                         
                
               

                               
                                                              
                                                      
                                                                            
             
               
                                                    
                                               
                   
                  
                                  
                                
                                
                                                  
                   
                           
                                                                           

                                                   
                                                                                                    
                                                                                      
             
           
                                                                                              
         
                                         
                                              
               
                                         
           

                                                                   
                                             
                                                  
                                      
                                       
