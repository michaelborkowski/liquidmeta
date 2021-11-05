time liquid --normal --interpreter   Basics.hs		
time liquid --normal --interpreter   Semantics.hs
time liquid --normal --interpreter   SystemFTyping.hs 	
time liquid --normal --interpreter   WellFormedness.hs		# much faster
time liquid --normal --interpreter   BasicPropsSubstitution.hs

time liquid --normal --interpreter   PrimitivesFTyping.hs
time liquid --normal --interpreter   PrimitivesWFTypeAnd.hs		# new ple on prim files
time liquid --normal --interpreter   PrimitivesWFTypeOr.hs
time liquid --normal --interpreter   PrimitivesWFTypeNot.hs
time liquid --normal --interpreter   PrimitivesWFTypeEqv.hs

time liquid --normal --interpreter   PrimitivesWFTypeLeq.hs
time liquid --normal --interpreter   PrimitivesWFTypeLeqn.hs
time liquid --normal --interpreter   PrimitivesWFTypeEq.hs
time liquid --normal --interpreter   PrimitivesWFTypeEqn.hs
time liquid --normal --interpreter   PrimitivesWFType.hs

time liquid --normal --interpreter   BasicPropsEnvironments.hs
time liquid --normal --interpreter   BasicPropsWellFormedness.hs
time liquid --normal --interpreter   SystemFLemmasFTyping.hs
time liquid --normal --interpreter   SystemFLemmasSubstitution.hs  
time liquid --normal --interpreter   SystemFSoundness.hs

time liquid --normal --interpreter   Typing.hs  
time liquid --normal --interpreter   BasicPropsCSubst.hs 
time liquid --normal --interpreter   BasicPropsDenotes.hs 
time liquid --normal --interpreter   PrimitivesSemantics.hs
time liquid --normal --interpreter   Implications.hs

time liquid --normal --interpreter   Entailments.hs 
time liquid --normal --interpreter   LemmasChangeVarWF.hs
time liquid --normal --interpreter   LemmasChangeVarWFEnv.hs
time liquid --normal --interpreter   LemmasChangeVarEnt.hs
time liquid --normal --interpreter   LemmasWeakenWF.hs

time liquid --normal --interpreter   LemmasWeakenEnt.hs
time liquid --normal --interpreter   LemmasWellFormedness.hs
time liquid --normal --interpreter   LemmasTyping.hs
time liquid --normal --interpreter   LemmasSubtyping.hs
time liquid --normal --interpreter   SubstitutionLemmaWF.hs

time liquid --normal --interpreter   LemmasChangeVarTyp.hs
time liquid --normal --interpreter   LemmasWeakenTyp.hs
time liquid --normal --interpreter   DenotationsSelfify.hs
time liquid --normal --interpreter   PrimitivesDenotationsAnd.hs
time liquid --normal --interpreter   PrimitivesDenotationsOr.hs

time liquid --normal --interpreter   PrimitivesDenotationsEqv.hs
time liquid --normal --interpreter   PrimitivesDenotationsLeq.hs
time liquid --normal --interpreter   PrimitivesDenotationsEq.hs
time liquid --normal --interpreter   PrimitivesDenotations.hs
time liquid --normal --interpreter   DenotationsSoundness.hs

time liquid --normal --interpreter   LemmasExactness.hs
time liquid --normal --interpreter   SubstitutionLemmaEnt.hs
time liquid --normal --interpreter   SubstitutionLemmaTyp.hs
time liquid --normal --interpreter   LemmasNarrowingEnt.hs
time liquid --normal --interpreter   LemmasNarrowingTyp.hs

time liquid --normal --interpreter   --max-case-expand=4 LemmasTransitive.hs
time liquid --normal --interpreter   LemmasSubtypeClosed.hs
time liquid --normal --interpreter   LemmasInvertLambda.hs
time liquid --normal --interpreter   PrimitivesRefinements.hs
time liquid --normal --interpreter   PrimitivesDeltaTyping.hs

time liquid --normal --interpreter   MainTheorems.hs
