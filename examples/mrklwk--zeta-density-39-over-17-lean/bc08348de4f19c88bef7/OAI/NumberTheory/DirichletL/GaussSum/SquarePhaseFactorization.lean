module
public import OAI.NumberTheory.DirichletL.GaussSum.CubicTrace
public import OAI.NumberTheory.DirichletL.Fourier.PositiveLogProfiles
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
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped ContDiff FourierTransform SchwartzMap
open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open MeasureTheory Set
open scoped BigOperators

namespace ActualEisensteinCubic

                                                              
                                                                     
                       
                                                 
                                                              
               
          
            
                                               
                                                                         
                                      

                                              
                                                                      
                                              
                 
                   
                                                
                                                                  
                           
                                                                          
            
                                               

                                                                      
                                                                
            
                                   
                                                         
                                                      
                                                              
                                                              
                                       

                                                                
                               
                                  
                                                 
           
                                                                             
                                                                  
              
                      
                                                 
                                                                
                                           
                                                                             
                                                              
                                                 
             
                                                
                                                    
                     
                                                  
                                                   
                                                                  
                                                                              
                                                                
                                                                                   
                               
                                                        
                                                            
                              
                                                                  
                  
                                                    
                                                
                       
                                 
                    
                                                 
                                                          

                                        
                                    
                                         
                  
                                                     

                                             
                                                               
                                                             
                                                                     
           
                                               
                                             
                                                                 
                                                      
                                                        
                                                                             
                                                                             
                                                       
                                       

                                     
                                                               
                                                             
                                                       
                                             
           
                                                                               
                 
                 

                                                        
                                           
                                       
                                        
                         
           
      
                                                                       
                                          

                                                         
                                                        

                                 
                                                         
                                   
                                                                      
                           

                                                     
                                             
                                                   
          
                        
           
                                                    
                                                                   
                                                                    

                                            
                                               
                                               
                                                               
                                                                 
                                                                       
                                                
                                                      
           
                       
                                                                   
                                                                   
                                                                
                                                                     
                        
            
                                                                        
                                                                          
                        
            
                                                                        
                                                                           
                                                   
                                                                 
                                             
                        
                                                  
                                                      
              
                                     
                                                                                            
                                                   
                                                                                 
                                                              
                                                     
                                                                           
                                                                    
                                                                     
                                       
                                                                   
                                       
                                                                       
                                                       
                                                            
                                                                                                
                                                            
                                    
                               
                                                            
                                                     
                                                       
                                                             
           
                                                
                            
                     
              
                                             
                                               
                                                         
                             
                   
                                                                                   
                                                                                   
                                                                              
                                                                                    
                                                                                           
             

                                 
                                               
                                               
                                                                 
                                                                       
                                                
                                                      
                      
                                                                          
                                                                            
                                               
                                                                                 
                                                        
                                                                            
                                     
                                                                           
                                     

                                              
                                               
                                               
                                                                 
                                                                       
                                                            
                                                                  
                                                                     
                                                                                      
                                                                                  
       
                                                                     
                                                                                      
                                                                                  
       
                                                                                          

def cubicTwoIdeal : Ideal O := Ideal.span {(-2 : O)}

instance cubicTwoIdeal_isMaximal : cubicTwoIdeal.IsMaximal := by
  rcases rational_prime_factor_cases 2 Nat.prime_two with hm |
      ⟨a, b, _, _, _, ha, _, _, _⟩
  · simpa only [cubicTwoIdeal, Ideal.span_singleton_neg, Nat.cast_ofNat] using hm
  · have hin : (Ideal.span {a} : Ideal O) ∈ {I : Ideal O | Ideal.absNorm I = 2} := by
      change Ideal.absNorm (Ideal.span {a}) = 2
      rwa [← qNat_eq_absNorm_span]
    rw [ShortDraftHeckeBridge.norm_p_fiber_inert Nat.prime_two (by decide)] at hin
    exact False.elim hin

                                                         
                                                             
                                   

                                                                           
                                                                       
                                                         
                                           
                                                
                                     
                                             
                                                                        
                                                                               
                                                                   

                                         
                                                    
                                                                       
                                                           
                                   
                                                                                              
                                                                                     
                                  
        
                                                                       
                            
                                                                                             
         
                                                                          
                                          

                                              
                                                                       
                                           
                                          
                                                
                                                                                  
                                                                               
                                                               
                      
                             
            
                                                                                         

                                                   
                                                                       
                                           
                                          
                                              
                                           
                                                                                          
                                                      
                                                
                                           
                                                                     
                                                      
                                                       
                                                                                            

end ActualEisensteinCubic

open scoped BigOperators Classical

namespace IdealGaussCRT

                                                             
                                                      
                                    
                                            
                          
                                                             
      
                                                                   
                                
               
                                                  
                                       
                                                                     
                              
                                                                        
                                                                                           

                                                                          
                                                   
                                    
                                          
                                                            
                                                                                             
                              
                              
                                                                       
                                      
                             
           
                                                     
                                               
                                                                   
                                                                               

end IdealGaussCRT

namespace QuadraticGaussRay

abbrev O := ActualEisensteinCubic.O
open ActualEisensteinCubic ConcreteTraceCRT FiniteGaussPhase ActualEisensteinCoordinates

                                                     
                                                           
                                       
                                                                            
                                            
                                                        
                                                        
                                                                                      
                   
                                                                  
                                                              
                                                          
                                                                    
                                                                      
                                   
                                                 
                                                 
                                   
                                                                              
                                                                                             
         
                                               
                                                              
                                       
                                                                       

                                                                
                                       
                                                                         
                                     
                                                
          

                                              
                                                     
                                                                 
                                                                                
                                                  
             
               
                                                                     
                                                                                 

                                                                
                                                    

                                                          
                                                              
                                                                                         
                                                                                         
                                    
         
                                  
                                                    

                                                                            
                                                                                   
                                                                  

                                               
                                                           
                                       
                                                                            
                                            
                                                        
                                                        
                                                  
                                                                          
                                

open ActualEisensteinCubic ConcreteTraceCRT FiniteGaussPhase ActualEisensteinCoordinates

                                              
                                       
                                                              
                                                                                
                             
                                              
                           
      
                                      
                                      

                                                          
                                                           
                                                                        

                                                                    
                               
                     
                                                      
                                             
        
                                               
                                                                                   
                                     
                                                   
                       
                                                                 
                                                        

                                                
                                                     
                                                                            
                                                                                       

                                                                                       
                                                                                            

                                                
                                                                                       

                                                             
                                     

                                        
                                                           
                                       
                                                                            
                                            
                                                      
                                            
                                                                              
                        
                                                                                          
                                               
                                                                  
                                 
     

                                          
                                         
                                                                       
                                                                            
                                            
                                                      
                                          
                                                                       
                                                                            
                                            
                                                      
                                          
                                                      
                                                                               
                                                                      
                                                                          

                                           
                                                           
                                       
                                                                            
                                            
                                                      
                                            
                                       
                                                                                  
                                                                 

end QuadraticGaussRay

end

end OAI
