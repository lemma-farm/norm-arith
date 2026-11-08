module

public import AmbidextrousSofa.Analysis.EndpointTrimming
public import AmbidextrousSofa.Analysis.PolygonEnvelope

@[expose] public section

/-!
# Inward endpoint operations preserve the finite polygon class

A cut only changes the two displayed endpoint walls. Horizontal erosion
tightens each displayed upper wall by the positive horizontal component
of its normal. These are exact identities of actual sets. The new displayed
heights need not be attained supports; replacing every height by its actual
support gives the same polygon, including redundant inequalities.
-/

noncomputable section

open Set

namespace AmbidextrousSofa

namespace FinitePolygon

variable {ι : Type*}

                                                                        
                                                 
                                                                                   
                  
                                                     
                                                                                      
       
                                                                                  
             
                                             
                                               
                                                                                               
                            
                                                                                              
                                                                 
                                                                               

                                                                                  
                  
                                                    
                                                                                         
       
                                                                                 
             
                                             
                                               
                                                                                                  
                            
                                                                                              
                                                                    
                                                                                  

end FinitePolygon

end AmbidextrousSofa
