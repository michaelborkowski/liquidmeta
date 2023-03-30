echo "Checking the SystemRF Mechanization"
echo "-----------------------------------------------"
echo "Version 1.2: Full 2022 RF proof + If Statements + Circular WF-Typing"
echo "-----------------------------------------------"

echo "(01) Checking BasicDefinitions.v ..."
coqc -R SystemRF SystemRF SystemRF/BasicDefinitions.v
echo "(02) Checking Names.v ..."
coqc -R SystemRF SystemRF SystemRF/Names.v
echo "(03) Checking Strengthenings.v ..."
coqc -R SystemRF SystemRF SystemRF/Strengthenings.v
echo "(04) Checking LocalClosure.v ..."
coqc -R SystemRF SystemRF SystemRF/LocalClosure.v
echo "(05) Checking Semantics.v ..."
coqc -R SystemRF SystemRF SystemRF/Semantics.v
echo "(06) Checking SystemFWellFormedness.v ..."
coqc -R SystemRF SystemRF SystemRF/SystemFWellFormedness.v
echo "(07) Checking SystemFTyping.v ..."
coqc -R SystemRF SystemRF SystemRF/SystemFTyping.v
echo "(08) Checking PrimitivesFTyping.v ..."
coqc -R SystemRF SystemRF SystemRF/PrimitivesFTyping.v
echo "(09) Checking BasicPropsSubstitution.v ..."
coqc -R SystemRF SystemRF SystemRF/BasicPropsSubstitution.v
echo "(10) Checking BasicPropsEnvironments.v ..."
coqc -R SystemRF SystemRF SystemRF/BasicPropsEnvironments.v
echo "(11) Checking BasicPropsWFFT.v ..."
coqc -R SystemRF SystemRF SystemRF/BasicPropsWFFT.v
echo "(12) Checking SystemFLemmasWellFormedness.v ..."
coqc -R SystemRF SystemRF SystemRF/SystemFLemmasWellFormedness.v
echo "(13) Checking SystemFLemmasWeaken.v ..."
coqc -R SystemRF SystemRF SystemRF/SystemFLemmasWeaken.v
echo "(14) Checking SystemFLemmasSubstitution.v ..."
coqc -R SystemRF SystemRF SystemRF/SystemFLemmasSubstitution.v
echo "(15) Checking SystemFSoundness.v ..."
coqc -R SystemRF SystemRF SystemRF/SystemFSoundness.v

#echo "Checking WellFormedness.v ..."
#coqc -R SystemRF SystemRF SystemRF/WellFormedness.v
echo "(16) Checking Typing.v ..."
coqc -R SystemRF SystemRF SystemRF/Typing.v
echo "(17) Checking BasicPropsWellFormedness.v ..."
coqc -R SystemRF SystemRF SystemRF/BasicPropsWellFormedness.v
#echo "Checking LemmasWeakenWF.v ..."
#coqc -R SystemRF SystemRF SystemRF/LemmasWeakenWF.v
#echo "Checking LemmasWeakenWFTV.v ..."
#coqc -R SystemRF SystemRF SystemRF/LemmasWeakenWFTV.v
echo "(18) Checking LemmasWeaken.v ..."
coqc -R SystemRF SystemRF SystemRF/LemmasWeaken.v
#echo "(19) Checking LemmasWeakenTV.v ..."
#coqc -R SystemRF SystemRF SystemRF/LemmasWeakenTV.v
#echo "Checking LemmasWellFormedness.v ..."
#coqc -R SystemRF SystemRF SystemRF/LemmasWellFormedness.v
#echo "Checking PrimitivesWFType.v ..."
#coqc -R SystemRF SystemRF SystemRF/PrimitivesWFType.v  
#echo "Checking SubstitutionLemmaWF.v ..."
#coqc -R SystemRF SystemRF SystemRF/SubstitutionLemmaWF.v
#echo "Checking SubstitutionLemmaWFTV.v ..."
#coqc -R SystemRF SystemRF SystemRF/SubstitutionLemmaWFTV.v
#echo "Checking LemmasTyping.v ..."
#coqc -R SystemRF SystemRF SystemRF/LemmasTyping.v
#echo "Checking LemmasSubtyping.v ..."
#coqc -R SystemRF SystemRF SystemRF/LemmasSubtyping.v
#echo "Checking LemmasExactness.v ..."
#coqc -R SystemRF SystemRF SystemRF/LemmasExactness.v  
#echo "Checking LemmasExactnessSubst.v ..."
#coqc -R SystemRF SystemRF SystemRF/LemmasExactnessSubst.v  
#echo "Checking SubstitutionLemmaTyp.v ..."
#coqc -R SystemRF SystemRF SystemRF/SubstitutionLemmaTyp.v
#echo "Checking SubstitutionLemmaTypTV.v ..."
#coqc -R SystemRF SystemRF SystemRF/SubstitutionLemmaTypTV.v
#echo "Checking LemmasNarrowing.v ..."
#coqc -R SystemRF SystemRF SystemRF/LemmasNarrowing.v
#echo "Checking LemmasTransitive.v ..."
#coqc -R SystemRF SystemRF SystemRF/LemmasTransitive.v
#echo "Checking LemmasInversion.v ..."
#coqc -R SystemRF SystemRF SystemRF/LemmasInversion.v
#echo "Checking PrimitivesDeltaTyping.v ..."
#coqc -R SystemRF SystemRF SystemRF/PrimitivesDeltaTyping.v
#echo "Checking MainTheorems.v ..."
#coqc -R SystemRF SystemRF SystemRF/MainTheorems.v

#echo "Up next: Circular Judgments?"
#echo "Up next: Implement the Denotational Semantics Development"
