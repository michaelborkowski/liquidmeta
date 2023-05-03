echo "Checking the SystemRF Mechanization"
echo "-----------------------------------------------"
echo "Version 1.1: Full 2022 RF proof + If Statements"
echo "-----------------------------------------------"

echo "Skipping SystemRF Main Development"
echo "Checking the Denotational Semantics Development"
echo "Checking ClosingSubstitutions.v ..."
coqc -Q SystemRF SystemRF -R Denotations Denotations Denotations/ClosingSubstitutions.v
echo "Checking Denotations.v ..."
coqc -Q SystemRF SystemRF -R Denotations Denotations Denotations/Denotations.v
echo "Checking BasicPropsCSubst.v ..."
coqc -Q SystemRF SystemRF -R Denotations Denotations Denotations/BasicPropsCSubst.v
echo "Checking BasicPropsSemantics.v ..."
coqc -Q SystemRF SystemRF -R Denotations Denotations Denotations/BasicPropsSemantics.v
echo "Checking PrimitivesSemantics.v ..."
coqc -Q SystemRF SystemRF -R Denotations Denotations Denotations/PrimitivesSemantics.v
echo "Checking PrimitivesDenotations.v ..."
coqc -Q SystemRF SystemRF -R Denotations Denotations Denotations/PrimitivesDenotations.v
echo "Checking DenotationalSoundness.v ..."
coqc -Q SystemRF SystemRF -R Denotations Denotations Denotations/DenotationalSoundness.v
echo "Checking MainProperties.v ..."
coqc -Q SystemRF SystemRF -R Denotations Denotations Denotations/MainProperties.v
