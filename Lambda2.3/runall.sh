time liquid --normal Basics.hs
time liquid --normal LocalClosure.hs                                    # TODO: lots lots lots
time liquid --normal Strengthenings.hs
time liquid --normal Semantics.hs
time liquid --normal SystemFWellFormedness.hs

time liquid --normal SystemFTyping.hs 
time liquid --normal BasicPropsSubstitution.hs                          # TODO: lots lots lots lots 
time liquid --normal PrimitivesFTyping.hs
time liquid --normal BasicPropsEnvironments.hs	                        # TODO: lots lots lots lots
time liquid --normal CheckSynth.hs                                      # TODO: many errors

time liquid --normal WellFormedness.hs                                  
time liquid --normal SynthWellFormed.hs                                 # TODO: errors
time liquid --normal PrimitivesWFType.hs                                # add more later
time liquid --normal BasicPropsWellFormedness.hs                        # TODO: lots lots lots lots
time liquid --normal SystemFLemmasWellFormedness.hs                     # TODO: lots lots lots lots 

time liquid --normal SystemFLemmasWeaken.hs                             
time liquid --normal SystemFLemmasSubstitution.hs                       # TODO: lots lots lots 
###time liquid --normal          SystemFSoundness.hs

#####time liquid --normal          Typing.hs  
#####time liquid --normal --oldple BasicPropsCSubst.hs                 
#####time liquid --normal --oldple BasicPropsDenotes.hs                        
#####time liquid --normal --oldple BasicPropsEraseTyping.hs		
#####time liquid --normal          PrimitivesSemantics.hs

#####time liquid --normal --oldple LemmasChangeVarWF.hs
#####time liquid --normal --oldple LemmasChangeVarWFEnv.hs
#####time liquid --normal --oldple LemmasChangeVarEnt.hs
#####time liquid --normal --oldple LemmasWeakenWF.hs
#####time liquid --normal --oldple LemmasWeakenWFTV.hs

#####time liquid --normal --oldple LemmasWeakenEnt.hs
#####time liquid --normal --oldple LemmasWellFormedness.hs
#####time liquid --normal --oldple Implications.hs 
#####time liquid --normal --oldple Entailments.hs                    
#####time liquid --normal          SubtypingFromEntailments.hs       

#####time liquid --normal --oldple SubstitutionLemmaWF.hs
#####time liquid --normal --oldple SubstitutionLemmaWFTV.hs
#####time liquid --normal --oldple LemmasTyping.hs
#####time liquid --normal          SubstitutionWFAgain.hs	
#####time liquid --normal --oldple LemmasChangeVarTyp.hs		

#####
#####time liquid --normal --oldple LemmasWeakenTyp.hs		
#####time liquid --normal --oldple LemmasWeakenTypTV.hs
#####time liquid --normal --oldple LemmasSubtyping.hs
#####time liquid --normal          DenotationsSelfify.hs		

#####time liquid --normal          PrimitivesDenotationsAnd.hs
#####time liquid --normal          PrimitivesDenotationsOr.hs
#####time liquid --normal          PrimitivesDenotationsNot.hs
#####time liquid --normal          PrimitivesDenotationsEqv.hs
#####time liquid --normal          PrimitivesDenotationsLeq.hs

#####time liquid --normal          PrimitivesDenotationsEq.hs
#####time liquid --normal          PrimitivesDenotationsEql.hs
#####time liquid --normal          PrimitivesDenotations.hs
#####time liquid --normal --oldple SubstitutionLemmaWFEnv.hs
#####time liquid --normal --oldple DenotationsSoundnessSBase.hs

#####time liquid --normal --oldple DenotationsSoundness.hs
#####time liquid --normal          LemmasExactness.hs
#####time liquid --normal --oldple SubstitutionLemmaEnt.hs
#####time liquid --normal --oldple SubstitutionLemmaEntTV.hs
#####time liquid --normal --oldple SubstitutionLemmaTyp.hs

#####time liquid --normal --oldple EntailmentsExtra.hs
#####time liquid --normal --oldple EntailmentsExtra2.hs
#####time liquid --normal --oldple SubstitutionLemmaTypTV.hs
#####time liquid --normal          LemmasNarrowingEnt.hs
#####time liquid --normal --oldple LemmasNarrowingTyp.hs

#####time liquid --normal --oldple LemmasTransitive.hs
#####time liquid --normal          LemmasSubtypeClosed.hs
#####time liquid --normal --oldple LemmasInvertLambda.hs
#####time liquid --normal          PrimitivesRefinements.hs
#####time liquid --normal          PrimitivesDeltaTyping.hs
#####time liquid --normal          MainTheorems.hs
