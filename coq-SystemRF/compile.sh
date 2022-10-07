echo "Checking the SystemRF Mechanization"
echo "-----------------------------------"

echo "Checking BasicDefinitions.v ..."
coqc -R SystemRF SystemRF SystemRF/BasicDefinitions.v
echo "Checking Names.v ..."
coqc -R SystemRF SystemRF SystemRF/Names.v
echo "Checking Strengthenings.v ..."
coqc -R SystemRF SystemRF SystemRF/Strengthenings.v
echo "Checking LocalClosure.v ..."
coqc -R SystemRF SystemRF SystemRF/LocalClosure.v
echo "Checking Semantics.v ..."
coqc -R SystemRF SystemRF SystemRF/Semantics.v
echo "Checking SystemFWellFormedness.v ..."
coqc -R SystemRF SystemRF SystemRF/SystemFWellFormedness.v
echo "Checking SystemFTyping.v ..."
coqc -R SystemRF SystemRF SystemRF/SystemFTyping.v
echo "Checking WellFormedness.v ..."
coqc -R SystemRF SystemRF SystemRF/WellFormedness.v
echo "Checking PrimitivesFTyping.v ..."
coqc -R SystemRF SystemRF SystemRF/PrimitivesFTyping.v
echo "Checking BasicPropsSubstitution.v ..."
coqc -R SystemRF SystemRF SystemRF/BasicPropsSubstitution.v
echo "Checking BasicPropsEnvironments.v ..."
coqc -R SystemRF SystemRF SystemRF/BasicPropsEnvironments.v
echo "Checking BasicPropsWellFormedness.v ..."
coqc -R SystemRF SystemRF SystemRF/BasicPropsWellFormedness.v
echo "Checking SystemFLemmasWellFormedness.v ..."
coqc -R SystemRF SystemRF SystemRF/SystemFLemmasWellFormedness.v
echo "Checking SystemFLemmasWeaken.v ..."
coqc -R SystemRF SystemRF SystemRF/SystemFLemmasWeaken.v
echo "Checking SystemFLemmasSubstitution.v ..."
coqc -R SystemRF SystemRF SystemRF/SystemFLemmasSubstitution.v
echo "Checking SystemFSoundness.v ..."
coqc -R SystemRF SystemRF SystemRF/SystemFSoundness.v
echo "Checking LemmasWeakenWF.v ..."
coqc -R SystemRF SystemRF SystemRF/LemmasWeakenWF.v
echo "Checking LemmasWeakenWFTV.v ..."
coqc -R SystemRF SystemRF SystemRF/LemmasWeakenWFTV.v
echo "Checking Typing.v ..."
coqc -R SystemRF SystemRF SystemRF/Typing.v
echo "Checking LemmasWellFormedness.v ..."
coqc -R SystemRF SystemRF SystemRF/LemmasWellFormedness.v
echo "Checking SubstitutionLemmaWF.v ..."
coqc -R SystemRF SystemRF SystemRF/SubstitutionLemmaWF.v
echo "Checking SubstitutionLemmaWFTV.v ..."
coqc -R SystemRF SystemRF SystemRF/SubstitutionLemmaWFTV.v
echo "Checking LemmasWeakenTyp.v ..."
coqc -R SystemRF SystemRF SystemRF/LemmasWeakenTyp.v
echo "Checking LemmasWeakenTypTV.v ..."
coqc -R SystemRF SystemRF SystemRF/LemmasWeakenTypTV.v
echo "Checking PrimitivesWFType.v ..."
coqc -R SystemRF SystemRF SystemRF/PrimitivesWFType.v  
echo "Checking LemmasTyping.v ..."
coqc -R SystemRF SystemRF SystemRF/LemmasTyping.v
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
echo "Checking PrimitivesDeltaTyping.v ..."
coqc -R SystemRF SystemRF SystemRF/PrimitivesDeltaTyping.v
echo "Checking MainTheorems.v ..."
coqc -R SystemRF SystemRF SystemRF/MainTheorems.v

echo "Up next: Implement the Denotational Semantics Development"
