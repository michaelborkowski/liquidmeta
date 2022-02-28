time liquid --normal Basics.hs
time liquid --normal LocalClosure.hs                                  
time liquid --normal Strengthenings.hs
time liquid --normal Semantics.hs
time liquid --normal SystemFWellFormedness.hs

time liquid --normal SystemFTyping.hs 
time liquid --normal BasicPropsSubstitution.hs                          
time liquid --normal PrimitivesFTyping.hs
time liquid --normal BasicPropsEnvironments.hs	                        
time liquid --normal WellFormedness.hs                                  

time liquid --normal BasicPropsWellFormedness.hs                      
time liquid --normal SystemFLemmasWellFormedness.hs                     
time liquid --normal SystemFLemmasWeaken.hs                             
time liquid --normal SystemFLemmasSubstitution.hs                      
#time liquid --normal SystemFSoundness.hs                               $ not needed without denotations

time liquid --normal Typing.hs                                          
time liquid --normal PrimitivesWFType.hs                               
time liquid --normal LemmasWeakenWF.hs
time liquid --normal LemmasWeakenWFTV.hs
time liquid --normal LemmasWellFormedness.hs	

time liquid --normal SubstitutionLemmaWF.hs
time liquid --normal SubstitutionLemmaWFTV.hs
time liquid --normal LemmasTyping.hs
time liquid --normal LemmasWeakenTyp.hs		
time liquid --normal LemmasWeakenTypTV.hs

time liquid --normal LemmasSubtyping.hs                                 
time liquid --normal LemmasExactness.hs             
time liquid --normal LemmasExactnessSubst.hs                        
time liquid --normal SubstitutionLemmaTyp.hs
time liquid --normal SubstitutionLemmaTypTV.hs

time liquid --normal LemmasNarrowingTyp.hs
time liquid --normal LemmasTransitive.hs
time liquid --normal LemmasInvertLambda.hs
time liquid --normal PrimitivesDeltaTyping.hs
time liquid --normal MainTheorems.hs
