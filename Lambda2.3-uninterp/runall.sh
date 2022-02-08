time liquid --normal Basics.hs
time liquid --normal LocalClosure.hs                                    # TODO: lots lots lots
time liquid --normal Strengthenings.hs
time liquid --normal Semantics.hs
time liquid --normal SystemFWellFormedness.hs

time liquid --normal SystemFTyping.hs 
time liquid --normal BasicPropsSubstitution.hs                          # TODO: various
time liquid --normal PrimitivesFTyping.hs
time liquid --normal BasicPropsEnvironments.hs	                        # TODO: various
time liquid --normal WellFormedness.hs                                  

time liquid --normal BasicPropsWellFormedness.hs                        # TODO: various if needed
time liquid --normal SystemFLemmasWellFormedness.hs                     
time liquid --normal SystemFLemmasWeaken.hs                             
time liquid --normal SystemFLemmasSubstitution.hs                      
time liquid --normal SystemFSoundness.hs

time liquid --normal Typing.hs                                          # TODO: eqlPred/self lemmata
time liquid --normal PrimitivesWFType.hs                                # add more later
#####time liquid --normal --oldple BasicPropsEraseTyping.hs		
#####time liquid --normal          PrimitivesSemantics.hs
time liquid --normal LemmasWeakenWF.hs

time liquid --normal LemmasWeakenWFTV.hs
time liquid --normal LemmasWellFormedness.hs				# TODO: various
time liquid --normal SubstitutionLemmaWF.hs
time liquid --normal SubstitutionLemmaWFTV.hs
time liquid --normal LemmasTyping.hs					# TODO: various

#####time liquid --normal          SubstitutionWFAgain.hs	
time liquid --normal LemmasWeakenTyp.hs		
time liquid --normal LemmasWeakenTypTV.hs
###time liquid --normal LemmasSubtyping.hs                                 # TODO: many
#####time liquid --normal --oldple SubstitutionLemmaWFEnv.hs
#time liquid --normal LemmasExactness.hs                                 # TODO: lots

#####time liquid --normal --oldple SubstitutionLemmaTyp.hs
#####time liquid --normal --oldple EntailmentsExtra.hs
#####time liquid --normal --oldple EntailmentsExtra2.hs
#####time liquid --normal --oldple SubstitutionLemmaTypTV.hs
#####time liquid --normal --oldple LemmasNarrowingTyp.hs

#####time liquid --normal --oldple LemmasTransitive.hs
#####time liquid --normal          LemmasSubtypeClosed.hs
#####time liquid --normal --oldple LemmasInvertLambda.hs
#####time liquid --normal          PrimitivesRefinements.hs
#####time liquid --normal          PrimitivesDeltaTyping.hs
#####time liquid --normal          MainTheorems.hs
