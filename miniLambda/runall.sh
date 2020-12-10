time liquid --normal          Basics.hs		
time liquid --normal          Semantics.hs
time liquid --normal --oldple SystemFTyping.hs 	
time liquid --normal --oldple WellFormedness.hs		# much faster
time liquid --normal --oldple BasicPropsSubstitution.hs

time liquid --normal          PrimitivesFTyping.hs
time liquid --normal          PrimitivesWFTypeAnd.hs		# new ple on prim files
time liquid --normal          PrimitivesWFTypeOr.hs
time liquid --normal          PrimitivesWFTypeNot.hs
time liquid --normal          PrimitivesWFTypeEqv.hs

time liquid --normal          PrimitivesWFTypeLeq.hs
time liquid --normal          PrimitivesWFTypeLeqn.hs
time liquid --normal          PrimitivesWFTypeEq.hs
time liquid --normal          PrimitivesWFTypeEqn.hs
time liquid --normal          PrimitivesWFType.hs

time liquid --normal --oldple BasicPropsEnvironments.hs
time liquid --normal --oldple BasicPropsWellFormedness.hs
time liquid --normal --oldple SystemFLemmasFTyping.hs
time liquid --normal --oldple SystemFLemmasSubstitution.hs  
time liquid --normal --oldple SystemFSoundness.hs

time liquid --normal --oldple Typing.hs  
time liquid --normal --oldple BasicPropsCSubst.hs                         
time liquid --normal --oldple BasicPropsDenotes.hs                        
time liquid --normal --oldple PrimitivesSemantics.hs
time liquid --normal --oldple Implications.hs

time liquid --normal --oldple Entailments.hs                            
time liquid --normal --oldple LemmasChangeVarWF.hs
time liquid --normal --oldple LemmasChangeVarWFEnv.hs
time liquid --normal --oldple LemmasChangeVarEnt.hs
time liquid --normal --oldple LemmasWeakenWF.hs

time liquid --normal --oldple LemmasWeakenEnt.hs
time liquid --normal --oldple LemmasWellFormedness.hs
time liquid --normal --oldple LemmasTyping.hs
time liquid --normal --oldple LemmasSubtyping.hs
time liquid --normal --oldple SubstitutionLemmaWF.hs

time liquid --normal --oldple LemmasChangeVarTyp.hs
time liquid --normal --oldple LemmasWeakenTyp.hs
time liquid --normal --oldple DenotationsSelfify.hs
time liquid --normal --oldple PrimitivesDenotationsAnd.hs
time liquid --normal --oldple PrimitivesDenotationsOr.hs

time liquid --normal --oldple PrimitivesDenotationsEqv.hs
time liquid --normal --oldple PrimitivesDenotationsLeq.hs
time liquid --normal --oldple PrimitivesDenotationsEq.hs
time liquid --normal --oldple PrimitivesDenotations.hs
time liquid --normal --oldple DenotationsSoundness.hs

time liquid --normal --oldple LemmasExactness.hs
time liquid --normal --oldple SubstitutionLemmaEnt.hs
time liquid --normal --oldple SubstitutionLemmaType.hs
time liquid --normal --oldple LemmasNarrowingEnt.hs
time liquid --normal --oldple LemmasNarrowingTyp.hs

time liquid --normal --oldple --max-case-expand=4 LemmasTransitive.hs
time liquid --normal          LemmasSubtypeClosed.hs
time liquid --normal --oldple LemmasInvertLambda.hs
time liquid --normal          PrimitivesRefinements.hs
time liquid --normal          PrimitivesDeltaTyping.hs

time liquid --normal --oldple MainTheorems.hs
