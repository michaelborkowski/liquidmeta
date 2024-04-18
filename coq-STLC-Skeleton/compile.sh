echo "Checking the STLC Mechanization"
echo "-----------------------------------------------"
echo "Version 3.0: Full 2023 RF proof + Lists"
echo "-----------------------------------------------"

echo "Checking BasicDefinitions.v ..."
coqc -R STLC STLC STLC/BasicDefinitions.v
echo "Checking Names.v ..."
coqc -R STLC STLC STLC/Names.v
echo "Checking Strengthenings.v ..."
coqc -R STLC STLC STLC/Strengthenings.v
echo "Checking LocalClosure.v ..."
coqc -R STLC STLC STLC/LocalClosure.v
echo "Checking Semantics.v ..."
coqc -R STLC STLC STLC/Semantics.v
echo "Checking SystemFWellFormedness.v ..."
coqc -R STLC STLC STLC/SystemFWellFormedness.v
echo "Checking SystemFTyping.v ..."
coqc -R STLC STLC STLC/SystemFTyping.v
echo "Checking WellFormedness.v ..."
coqc -R STLC STLC STLC/WellFormedness.v
echo "Checking PrimitivesFTyping.v ..."
coqc -R STLC STLC STLC/PrimitivesFTyping.v
echo "Checking BasicPropsSubstitution.v ..."
coqc -R STLC STLC STLC/BasicPropsSubstitution.v
echo "Checking BasicPropsEnvironments.v ..."
coqc -R STLC STLC STLC/BasicPropsEnvironments.v
echo "Checking BasicPropsWellFormedness.v ..."
coqc -R STLC STLC STLC/BasicPropsWellFormedness.v
echo "Checking SystemFLemmasWellFormedness.v ..."
coqc -R STLC STLC STLC/SystemFLemmasWellFormedness.v
echo "Checking SystemFLemmasWeaken.v ..."
coqc -R STLC STLC STLC/SystemFLemmasWeaken.v
echo "Checking SystemFLemmasSubstitution.v ..."
coqc -R STLC STLC STLC/SystemFLemmasSubstitution.v
echo "Checking SystemFSoundness.v ..."
coqc -R STLC STLC STLC/SystemFSoundness.v
