echo "Checking the SystemRF Mechanization"
echo "-----------------------------------"

echo "Checking BasicDefinitions.v ..."
coqc -Q . SystemF BasicDefinitions.v
echo "Checking Names.v ..."
coqc -Q . SystemF Names.v
echo "Checking LocalClosure.v ..."
coqc -Q . SystemF LocalClosure.v
echo "Checking Semantics.v ..."
coqc -Q . SystemF Semantics.v
echo "Checking SystemFWellFormedness.v ..."
coqc -Q . SystemF SystemFWellFormedness.v
echo "Checking SystemFTyping.v ..."
coqc -Q . SystemF SystemFTyping.v
echo "Checking PrimitivesFTyping.v ..."
coqc -Q . SystemF PrimitivesFTyping.v
#echo "Checking BasicPropsSubstitution.v ..."
#coqc -Q . SystemF BasicPropsSubstitution.v
#echo "Checking BasicPropsEnvironments.v ..."
#coqc -Q . SystemF BasicPropsEnvironments.v
#echo "Checking BasicPropsWellFormedness.v ..."
#coqc -Q . SystemF BasicPropsWellFormedness.v
#echo "Checking SystemFLemmasWellFormedness.v ..."
#coqc -Q . SystemF SystemFLemmasWellFormedness.v
#echo "Checking SystemFLemmasWeaken.v ..."
#coqc -Q . SystemF SystemFLemmasWeaken.v
#echo "Checking SystemFLemmasSubstitution.v ..."
#coqc -Q . SystemF SystemFLemmasSubstitution.v
#echo "Checking SystemFSoundness.v ..."
#coqc -Q . SystemF SystemFSoundness.v
