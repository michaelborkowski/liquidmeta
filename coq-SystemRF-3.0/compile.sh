echo "Checking the SystemRF Mechanization"
echo "-----------------------------------------------"
echo "Version 3.0: Full 2023 RF proof + Lists"
echo "-----------------------------------------------"

echo "Checking BasicDefinitions.v ...                             (updated)"
coqc -R SystemRF SystemRF SystemRF/BasicDefinitions.v
echo "Checking Names.v ...                                        (updated)"
coqc -R SystemRF SystemRF SystemRF/Names.v
echo "Checking Strengthenings.v ...                               (updated)"
coqc -R SystemRF SystemRF SystemRF/Strengthenings.v
echo "Checking LocalClosure.v ...                                 (updated)"
coqc -R SystemRF SystemRF SystemRF/LocalClosure.v
echo "Checking Semantics.v ...                                    (updated)"
coqc -R SystemRF SystemRF SystemRF/Semantics.v
echo "Checking SystemFWellFormedness.v ...                        (updated)"
coqc -R SystemRF SystemRF SystemRF/SystemFWellFormedness.v
echo "Checking SystemFTyping.v ...                                (updated)"
coqc -R SystemRF SystemRF SystemRF/SystemFTyping.v
echo "Checking WellFormedness.v ...                               (updated)"
coqc -R SystemRF SystemRF SystemRF/WellFormedness.v
echo "Checking PrimitivesFTyping.v ...                            (updated)"
coqc -R SystemRF SystemRF SystemRF/PrimitivesFTyping.v
echo "Checking BasicPropsSubstitution.v ...                       (updated)"
coqc -R SystemRF SystemRF SystemRF/BasicPropsSubstitution.v
echo "Checking BasicPropsEnvironments.v ...                       (updated)"
coqc -R SystemRF SystemRF SystemRF/BasicPropsEnvironments.v
echo "Checking BasicPropsWellFormedness.v ...                     (updated)"
coqc -R SystemRF SystemRF SystemRF/BasicPropsWellFormedness.v
echo "Checking SystemFLemmasWellFormedness.v ..."
coqc -R SystemRF SystemRF SystemRF/SystemFLemmasWellFormedness.v
echo "Checking SystemFLemmasWeaken.v ..."
coqc -R SystemRF SystemRF SystemRF/SystemFLemmasWeaken.v
echo "Checking SystemFLemmasSubstitution.v ..."
coqc -R SystemRF SystemRF SystemRF/SystemFLemmasSubstitution.v
echo "Checking SystemFSoundness.v ..."
coqc -R SystemRF SystemRF SystemRF/SystemFSoundness.v
echo "Checking Typing.v ..."
coqc -R SystemRF SystemRF SystemRF/Typing.v
echo "Checking LemmasWeakenWF.v ..."
coqc -R SystemRF SystemRF SystemRF/LemmasWeakenWF.v
echo "Checking LemmasWeakenWFTV.v ..."
coqc -R SystemRF SystemRF SystemRF/LemmasWeakenWFTV.v
echo "Checking LemmasWellFormedness.v ..."
coqc -R SystemRF SystemRF SystemRF/LemmasWellFormedness.v
echo "Checking PrimitivesWFType.v ..."
coqc -R SystemRF SystemRF SystemRF/PrimitivesWFType.v  
echo "Checking SubstitutionLemmaWF.v ..."
coqc -R SystemRF SystemRF SystemRF/SubstitutionLemmaWF.v
echo "Checking SubstitutionLemmaWFTV.v ..."
coqc -R SystemRF SystemRF SystemRF/SubstitutionLemmaWFTV.v
echo "Checking LemmasTyping.v ..."
coqc -R SystemRF SystemRF SystemRF/LemmasTyping.v
echo "Checking LemmasWeakenTyp.v ..."
coqc -R SystemRF SystemRF SystemRF/LemmasWeakenTyp.v
echo "Checking LemmasWeakenTypTV.v ..."
coqc -R SystemRF SystemRF SystemRF/LemmasWeakenTypTV.v
echo "Checking LemmasSubtyping.v ..."
coqc -R SystemRF SystemRF SystemRF/LemmasSubtyping.v
echo "Checking LemmasExactness.v ..."
coqc -R SystemRF SystemRF SystemRF/LemmasExactness.v  
echo "Checking LemmasExactnessSubst.v ..."
coqc -R SystemRF SystemRF SystemRF/LemmasExactnessSubst.v  
echo "Checking SubstitutionLemmaTyp.v ..."
coqc -R SystemRF SystemRF SystemRF/SubstitutionLemmaTyp.v
echo "Checking SubstitutionLemmaTypTV.v ..."
coqc -R SystemRF SystemRF SystemRF/SubstitutionLemmaTypTV.v
echo "Checking LemmasNarrowing.v ..."
coqc -R SystemRF SystemRF SystemRF/LemmasNarrowing.v
echo "Checking LemmasTransitive.v ..."
coqc -R SystemRF SystemRF SystemRF/LemmasTransitive.v
echo "Checking LemmasInversion.v ..."
coqc -R SystemRF SystemRF SystemRF/LemmasInversion.v
#echo "Checking PrimitivesDeltaTyping.v ..."
#coqc -R SystemRF SystemRF SystemRF/PrimitivesDeltaTyping.v
#echo "Checking MainTheorems.v ..."
#coqc -R SystemRF SystemRF SystemRF/MainTheorems.v

echo "Up next: Implement the Denotational Semantics Development"
echo "Checking ClosingSubstitutions.v ..."
coqc -Q SystemRF SystemRF -R Denotations Denotations Denotations/ClosingSubstitutions.v
echo "Checking Denotations.v ..."
coqc -Q SystemRF SystemRF -R Denotations Denotations Denotations/Denotations.v
#echo "Checking PrimitivesSemantics.v ..."
#coqc -Q SystemRF SystemRF -R Denotations Denotations Denotations/PrimitivesSemantics.v
#echo "Checking BasicPropsCSubst.v ..."
#coqc -Q SystemRF SystemRF -R Denotations Denotations Denotations/BasicPropsCSubst.v
#echo "Checking BasicPropsDenotes.v ..."
#coqc -Q SystemRF SystemRF -R Denotations Denotations Denotations/BasicPropsDenotes.v
#echo "Checking EnvironmentSubstitutions.v ..."
#coqc -Q SystemRF SystemRF -R Denotations Denotations Denotations/EnvironmentSubstitutions.v
#echo "Checking BasicPropsSemantics.v ..."
#coqc -Q SystemRF SystemRF -R Denotations Denotations Denotations/BasicPropsSemantics.v
#echo "Checking LemmasWidening.v ..."
#coqc -Q SystemRF SystemRF -R Denotations Denotations Denotations/LemmasWidening.v
#echo "Checking MultiSubstitutionLemmas.v ..."
#coqc -Q SystemRF SystemRF -R Denotations Denotations Denotations/MultiSubstitutionLemmas.v
#echo "Checking LemmasDenotesEnv.v ..."
#coqc -Q SystemRF SystemRF -R Denotations Denotations Denotations/LemmasDenotesEnv.v
#echo "Checking PrimitivesDenotations.v ..."
#coqc -Q SystemRF SystemRF -R Denotations Denotations Denotations/PrimitivesDenotations.v
#echo "Checking SelfifyDenotations.v ..."
#coqc -Q SystemRF SystemRF -R Denotations Denotations Denotations/SelfifyDenotations.v
#echo "Checking DenotationalSoundness.v ..."
#coqc -Q SystemRF SystemRF -R Denotations Denotations Denotations/DenotationalSoundness.v

#echo "Examples"
#echo "Checking Abs.v"
#coqc -Q SystemRF SystemRF -Q Denotations Denotations -R Examples Examples Examples/Abs.v
