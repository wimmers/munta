all: munta.mlb UPPAAL_Reachability_Checker_patched.sml
	mlton munta.mlb

UPPAAL_Reachability_Checker_patched.sml: UPPAAL_Reachability_Checker.sml
	patch -i postprocessing.patch -o UPPAAL_Reachability_Checker_patched.sml