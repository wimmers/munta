all: munta.mlb UPPAAL_Model_Checker_patched.sml
	mlton munta.mlb
	chmod +x munta

UPPAAL_Reachability_Checker_patched.sml: UPPAAL_Reachability_Checker.sml
	patch -i postprocessing.patch -o UPPAAL_Reachability_Checker_patched.sml

UPPAAL_Model_Checker_patched.sml: UPPAAL_Model_Checker.sml
	patch -i postprocessing_mc.patch -o UPPAAL_Model_Checker_patched.sml