echo "Checking the SystemRF Mechanization"
echo "-----------------------------------------------"
echo "Version 3.0: Full 2023 RF proof + Lists"
echo "-----------------------------------------------"

echo "Up next: Implement the Bidirectional Typechecker / Proof Synthesizer"
echo "Checking Decidable.v ..."
coqc -Q SystemRF SystemRF -Q Denotations Denotations -R Bidirectional Bidirectional Bidirectional/Decidable.v
echo "Checking SynthWFFT.v ..."
coqc -Q SystemRF SystemRF -Q Denotations Denotations -R Bidirectional Bidirectional Bidirectional/SynthWFFT.v
#echo "Checking SynthFType.v ..."
#coqc -Q SystemRF SystemRF -Q Denotations Denotations -R Bidirectional Bidirectional Bidirectional/SynthFType.v
#echo "Checking SynthWFType.v ..."
#coqc -Q SystemRF SystemRF -Q Denotations Denotations -R Bidirectional Bidirectional Bidirectional/SynthWFType.v
#echo "Checking SynthTyping.v ..."
#coqc -Q SystemRF SystemRF -Q Denotations Denotations -R Bidirectional Bidirectional Bidirectional/SynthTyping.v

#echo "Examples"
#echo "Checking Abs.v"
#coqc -Q SystemRF SystemRF -Q Denotations Denotations -R Examples Examples Examples/Abs.v
