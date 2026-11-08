module
public import OAI.NumberTheory.DirichletL.Mellin.CompactScale
public import Mathlib
@[expose] public section

namespace OAI

noncomputable section

open scoped BigOperators
open MulChar AddChar
open scoped BigOperators
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped FourierTransform SchwartzMap
open Finset Complex
open scoped Classical
open scoped Classical
open Filter Real Asymptotics
open ActualEisensteinCubic
open Filter
open ActualEisensteinCubic RationalPrimeExtraction ShortDraftLatticeCount
open ActualEisensteinCubic ShortDraftLatticeCount
open Filter
open scoped Topology
open EisensteinEmbedding ConcreteTraceCRT ActualEisensteinCubic
open MulChar AddChar
open Filter Asymptotics
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter
open MulChar AddChar
open MulChar AddChar
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Filter Asymptotics
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics Ideal NumberField
open Filter
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics MeasureTheory
open scoped Topology

namespace CompactScaleBridge

section

open ConcretePrimeRowBridge ShortDraftHeckeBridge FiniteSFactor

                                    
                                                                 
                                                   
           
                     
                          
            
                                                     
                                                         
         
                                                      
                         
                                                                       
                                          
                                                               
           
        
                                                  
                             

                                   
                                        
                                              
                                                     
                        
                                                              
                                           
           
                             
                                     
             
             
                             
                                                
                                                                       
                        
             
                                       
          
                              
                                        
             
                                                          
                                         
                                
                 
                           
                                
                                                              
                            
                                                                   
                                      
                                               
                                                           
                                                                  
                                   
          

end

open ConcretePrimeRowBridge ShortDraftHeckeBridge Filter Asymptotics

                                                  
                                        
                                              
                                                     
                                   
                                                           
                                                         
                      
                                                                                 

                                              
                                                   
                          
                                
                                                                 
                                                    
                                              
                                  
                                   
                                                    
                            
                                                             
                                                  
                                               
                           
                               
                                                         
                                                                           
                                        
                                        
            
                                                                              
                                         
                                                          
                                                                
                                             
             
                                                                              
                                                     
                                                   
                                                               
                                                              
                   

end CompactScaleBridge

open Filter Asymptotics MeasureTheory
open scoped Topology

namespace ConcreteCompactWeight

noncomputable def bumpData : ContDiffBump (3 / 2 : ℝ) :=
  ⟨1 / 8, 1 / 4, by norm_num, by norm_num⟩

noncomputable def bump (y : ℝ) : ℝ := bumpData y

                                                       
                                                  
                                  

                                                           

                                             
                                 
                                          
                                                
                              

                                                                    
                       
                                
                   
                                  
                      
                                    
            
                                    
            

                                                                           

noncomputable def positiveExtension (y : ℝ) : ℝ :=
  1 + (y - 1) * Real.smoothTransition (2 * y - 1)

                                                                                 
                          
                                                                          
                          
                                         
                                                          

                                                                     
                          
                            
                                          
                                                
            
                         
                                            
                                                 
              
                                                          
                                                              
                                                                            
                                                                                
               

                                                   
                                 
                          
                                                                        
      

noncomputable def weight (ρ : ℂ) (y : ℝ) : ℂ :=
  (bump y : ℂ) * Complex.exp ((Real.log (positiveExtension y) : ℂ) * (-ρ))

                               
                                           
                                                                    
                                                     
                                    
                                                      
                                                                              
                                  
                                                               
                                              
                                    
                                                                                 
                                
                   

                                      
                                               
                                  

                                                     
                                                    
                      
                                              
                                         
                                                          
                                                
                                                 
                                   
        

                                       
                                                                    
                                   
                                                                    
              
                               
             
            
                                                              
                                                                 
               
                                                                 
                             
                     
                         
          
                                                
                                                         

                                             
                              

                                                               
                                                                      
                                                 

                                                                   
                                                                          
                              

                                                              
                                                               

                                                                 
                                                                           

                                   
                                     
                                                                   
                                                                    
                        

                                                             
                            
                                                            

                                                   
                                          
                                         
             
                                
                                              
                                  
              
                        
                                                      
                                           
                                                            
                                                                 
                                 
                                                                        
                              
         
                                                                       
                                                             

                                                                     
                                                                       
                                                                

                                                            
                          
                       
                                         
        
                       
                                         
        
                                                  
                                   
                                                 
                                              
                                                           
                                
                                                          
                                                               
                                         
           

end ConcreteCompactWeight

namespace CompactScaleBridge

section

open ConcreteCompactWeight

                                                       
                                                   
                                                
                                
                                                               
                                                    
           
                                   
                                                    
                            
                                                                      
                                          
                        
                           
                                         
                                              
                                
                                        
                                   
                                         
                                         

end

                                                             
                                                            
                                                
                                                   
                                    
                                                    
                                                                    
                                       
                                  
                                             
                                                              
                                    
                                         
                                    
                              
                           
                                                       
                                                          
                                                         
                                             
                                    
                                                        
                                     

end CompactScaleBridge

namespace ActualEisensteinCubic

open ShortDraftCusp

                                                       
                                                    
                                            
                  
                                                  
                                                         
                                         
                                           
                                             
                                             
                                                                        
                                              
                                        

end ActualEisensteinCubic

namespace TwoPassProfiles

                             
                             
                                          
                             
                                   
                                           
                           
                                                   
            

                              
                           
                                          
                                   
                                         
                                                             
            

                            
                  
                                              
                                               
            

                              
                             
                                          
                                          
                                                
                                                              
                                            
                                                    
                                                  
                                                                      
                                                   
                                               
                                                                                                  
                                                                                             
                                                                                        
                                                                                                         
                                                                            
                                                                        
                                 
      

                               
                         
                                          
                             
                                   
                                                      
                                            
                                       
                                     
                                                              
                                                   
                                               
                                                                                          
                                                                                     
                                                                                                     
                                                                        
                                 
      

                          
                                                 
                                         

                                                                 
                                                       
                                                       
                                                         

                    
                               
                                                                   
                                            
                                                    
                                                  
                                                 
      

                           
                                       
                               

                                                              
                                                       
                                     
                                       

                     
                           
                                                                 
                                            
                                       
                                     
                                                   
      

                         
                             
                                          
                                          
                                                
                                                   
                            
                                                             
                                                                
                                 
                                           

                          
                         
                                          
                             
                                   
                                           
                            
                                                           
                                                              
                           
                                           

                            
                                 
                              
                                                
                                                
                                                    
                                          
                                          
                                                
                         
                                           
                                                            
                
                                                       
                              
                                                               
                                             
                                 
            

                             
                           
                          
                                                
                                 
                                     
                                          
                             
                                   
                         
                                               
                                  
                
                                             
                              
                                                             
                                          
                           
            

end TwoPassProfiles

end

end OAI
