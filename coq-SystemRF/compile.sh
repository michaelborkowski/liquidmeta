echo "Checking BasicDefinitions.v ..."
coqc -Q . SystemRF BasicDefinitions.v
echo "Checking Names.v ..."
coqc -Q . SystemRF Names.v
echo "Checking Strengthenings.v ..."
coqc -Q . SystemRF Strengthenings.v
echo "Checking LocalClosure.v ..."
coqc -Q . SystemRF LocalClosure.v
echo "Checking Semantics.v ..."
coqc -Q . SystemRF Semantics.v
echo "Checking SystemFWellFormedness.v ..."
coqc -Q . SystemRF SystemFWellFormedness.v
echo "Checking SystemFTyping.v ..."
coqc -Q . SystemRF SystemFTyping.v
echo "Checking WellFormedness.v ..."
coqc -Q . SystemRF WellFormedness.v
echo "Checking PrimitivesFTyping.v ..."
coqc -Q . SystemRF PrimitivesFTyping.v
echo "Checking BasicPropsSubstitution.v ..."
coqc -Q . SystemRF BasicPropsSubstitution.v
echo "Checking BasicPropsEnvironments.v ..."
coqc -Q . SystemRF BasicPropsEnvironments.v
echo "Checking BasicPropsWellFormedness.v ..."
coqc -Q . SystemRF BasicPropsWellFormedness.v
echo "Checking SystemFLemmasWellFormedness.v ..."
coqc -Q . SystemRF SystemFLemmasWellFormedness.v
echo "Checking SystemFLemmasWeaken.v ..."
coqc -Q . SystemRF SystemFLemmasWeaken.v
echo "Checking SystemFLemmasSubstitution.v ..."
coqc -Q . SystemRF SystemFLemmasSubstitution.v
echo "Checking SystemFSoundness.v ..."
coqc -Q . SystemRF SystemFSoundness.v
echo "Checking LemmasWeakenWF.v ..."
coqc -Q . SystemRF LemmasWeakenWF.v
echo "Checking LemmasWeakenWFTV.v ..."
coqc -Q . SystemRF LemmasWeakenWFTV.v
echo "Checking Typing.v ..."
coqc -Q . SystemRF Typing.v
echo "Checking LemmasWellFormedness.v ..."
coqc -Q . SystemRF LemmasWellFormedness.v
echo "Checking SubstitutionLemmaWF.v ..."
coqc -Q . SystemRF SubstitutionLemmaWF.v
echo "Checking SubstitutionLemmaWFTV.v ..."
coqc -Q . SystemRF SubstitutionLemmaWFTV.v
echo "Checking LemmasWeakenTyp.v ..."
coqc -Q . SystemRF LemmasWeakenTyp.v
echo "Checking LemmasWeakenTypTV.v ..."
coqc -Q . SystemRF LemmasWeakenTypTV.v
echo "Checking PrimitivesWFType.v ..."
coqc -Q . SystemRF PrimitivesWFType.v  
echo "Checking LemmasTyping.v ..."
coqc -Q . SystemRF LemmasTyping.v
echo "Checking LemmasSubtyping.v ..."
coqc -Q . SystemRF LemmasSubtyping.v
echo "Checking LemmasExactness.v ..."
coqc -Q . SystemRF LemmasExactness.v  
echo "Checking LemmasExactnessSubst.v ..."
coqc -Q . SystemRF LemmasExactnessSubst.v  
echo "Checking SubstitutionLemmaTyp.v ..."
coqc -Q . SystemRF SubstitutionLemmaTyp.v
echo "Checking SubstitutionLemmaTypTV.v ..."
coqc -Q . SystemRF SubstitutionLemmaTypTV.v
echo "Checking LemmasNarrowing.v ..."
coqc -Q . SystemRF LemmasNarrowing.v
echo "Checking LemmasTransitive.v ..."
coqc -Q . SystemRF LemmasTransitive.v
echo " ..."
# coqc -Q . SystemRF LemmasInversion.v
echo " ..."
# coqc -Q . SystemRF PrimitivesDeltaTyping.v
echo " ..."
# coqc -Q . SystemRF
