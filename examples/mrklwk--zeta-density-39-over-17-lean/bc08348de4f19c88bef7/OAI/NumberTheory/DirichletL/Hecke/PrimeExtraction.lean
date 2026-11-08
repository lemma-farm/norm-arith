module
public import OAI.NumberTheory.DirichletL.Hecke.LocalEulerIdentities
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

namespace ShortDraftHeckeBridge

                                                 
                                                                
                                                
                                                     
                  
                                                                   
                                        
                                    
                                              
                      
                                               
                        
                            
                                                                   
                        
                                                     
                                            
                              

end ShortDraftHeckeBridge
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid

namespace FiniteSFactor

abbrev O := NumberField.RingOfIntegers (CyclotomicField 3 ℚ)

                                                   
                                                                     
                                                   
                                                                       
                                                                  
                                           
                                           
                                                                 
                                                                              
                                              
                                                                                
                                                 
                                                 
                                                         
                    
                                                                                    
                            

noncomputable def outsideWeight (S : Finset (Ideal O))
    (w : Ideal O → ℂ) (I : Ideal O) : ℂ := by
  classical
  exact if ∀ P ∈ S, ¬ P ∣ I then w I else 0

                                                
                                                 
                                                       
                               
                                                     
           
                                                   
                                          
                   
                                           
                                           
                   
                                            
                                                   
                       
                                                     
                       
                       
                                                  
                                                             
                      
                        
                             
                                 
                                                        
                        
                                                     
                  

noncomputable def fiber (n : ℕ) : Finset (Ideal O) :=
  (Ideal.finite_setOfPred_absNorm_eq (S := O) n).toFinset

                                                                                 
              

                                                                         
           
                                                                            

                                                                          
           
                                                          

                                                          
                                                                                         
           
                            

                                                           
                                                                         
           
                             

                                                                   
                                                      
                                               
                                         
                                                      

                                                              
                                           
                                                                    
             
                                                          
                                         
                                                      

                                                               
                               
                               
                                          
           
                                      
                                                  
                                                                        
              
                                       
                                                            
                                           
                                     
                                                                        
                                                   
                                           
                          
                             
                                         
                                                      
                                                 
              
                                          
                                          
                                           
                                    
                                                                              
                                        
                                                                            
              
                                        
              
                                         
                                            
                                            
                                             
                                                      
                                                                                
                                                              
                                                    
                                                    
              
                                              

open scoped Classical

                                                                                    
           
                                                

                                                                               
                                                    
                                                
                                                                        
           
                        
                            
            
                             
              
                           

                                                      
                     
                                          
                                                
             
                                              
                                                  
                                          
           
                              
                                      
                                                  
                                                     
                                 
                              
              
                                   
                                                         
                                   
                 
                                                          
                                                                        
                                                       
                              
              
                               
                
                             
      
                          
                                                    
                                                             
                                                              
               
         
                                                                     
                                              
                                                                     
                         
             
                                
                
                                            
                                                                              

                                                          
                     
                                          
                                                
             
                                                   
                                  
                                                                      
           
                                     
                                                            
                              
             
                                        
                                                    
                                                 
                                                               
                                            
                   
                
                                                         
                  
                                                                    
                                           
                         
                              
              
                     

open scoped Classical

noncomputable def outsideCoeff (S : Finset (Ideal O))
    (w : Ideal O → ℂ) (n : ℕ) : ℂ :=
  ∑ I ∈ fiber n, outsideWeight S w I

                                                                           
                                                            
                                                                       
                               
                                      
                            

                                                                     
                                                            
                                       
                                   
                                    
                 
                       
                                                                  
                          
                                                   
                         

                                                                     
                                             
                                              
                                         
           
                                      
                            
            
                     
                            
                                 
                              
                                  

                                                   
                                                            
                                     
                                          
                                                          
             
                                                        
                                  
                                                                             
                                                               
                                                  
                            
                                                                                 
                
                                          
                                                                   
                                                                             
                                
                                             
                                                               
                                                                  
             

end FiniteSFactor
namespace ShortDraftHeckeBridge

                                                       
                                                                      
                                  
                                                                                
      

                                                  
                                                                       
                                
                                                       
                                                                                  
      

                                               
                                
                                                  
                                                          
                                                         
                                                                      
                                  
                              
                                                                      
                                               
                                                          
                                                                    
                                            

end ShortDraftHeckeBridge

namespace DyadicTransfer

                                                          
                 

                                                    
                                       
                                                          
                                 
                                     
                                                        

                                                   
                                       
                                                      
                                     
                                                       

                                                       
                                
                                          
                                           
                  
           
                          
                
                                    
                          
                                                        
                                                                       
                     
                  
                 
          

                                 
                                       
                                       
                                                         
                                
                                                        
                        
                                              
                                             
                                              
                               
        
                                                  

                                                                           
                                                       

                                                     
                                       
                                              
                                    
                                                                     

                                                    
                                       
                                          
                                    
                                                                    

                                                          
                                                                
                              
                              
                                                 
                              
                                                     
                                     
                                                 
                                                        
                            
                                                     
      
                                                                              
                                                                        
                                    
              
                                  
                                                           
                                                                   
                                                    

                                                     
                   
                                       
                                       
                     
                                                                
                                                           
                                 
                             
                                                                  
                      
                            
            
                      
           
                                             
                                                      
                                                                     
                            
                       
                                                                 
                                       
             
                                                  
                
                  
                         
                                
        

                                 
                                                   
                                                      
             
                                       
                                                      
                                           
                                                           
                                 
                                       
                
                                         
                                         
        
                                         
                                                              
                                                     
                               
                  
                                                                 
                                                 
                                                        
                                           
                                            
                                                               
                 
                                             
                                   
        
                                             
                                                                  
                                                     
                               
                 
                     
                                                     
                             
                                     
                                                                            
                                                 
                           
      
                                        
                                            
                                           
                                                                  
                                                              
                                 
                                                                  

end DyadicTransfer

open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid

namespace FiniteSFactor

                                                                        
                                   
                                          
                                                          
             
                        
                                        
                                    
                                                                              
                                  
             
                                                                
                                                          
                                                 
                                                                  
                     
           
                                                    
                                                              
              
                                                  
                  
                                                                      
                                                                           
                                                                            
                                                                         
                         
                                           
                                
              

end FiniteSFactor

end

end OAI
