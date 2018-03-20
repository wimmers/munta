all: munta

munta: munta.mlb UPPAAL_Model_Checker_patched.sml
	mlton munta.mlb
	chmod +x munta

munta_int: munta_int.mlb Checker_int.sml UPPAAL_Model_Checker_int.sml
	mlton -output munta_int munta_int.mlb
	chmod +x munta_int

UPPAAL_Reachability_Checker_patched.sml: UPPAAL_Reachability_Checker.sml
	patch -i postprocessing.patch -o UPPAAL_Reachability_Checker_patched.sml

UPPAAL_Model_Checker_patched.sml: UPPAAL_Model_Checker.sml
	patch -i postprocessing_mc.patch -o UPPAAL_Model_Checker_patched.sml

Checker_int.sml: Checker.sml
	patch -i Checker_int.patch -o Checker_int.sml

UPPAAL_Model_Checker_int.sml: UPPAAL_Model_Checker_patched.sml
	patch -i UPPAAL_Model_Checker_int.patch -o UPPAAL_Model_Checker_int.sml UPPAAL_Model_Checker_patched.sml

munta_int.mlb: munta.mlb
	patch -i munta_int.patch -o munta_int.mlb