all: muntax

munta: munta.mlb UPPAAL_Model_Checker_patched.sml
	mlton -output muntab munta.mlb
	chmod +x munta

munta_int: munta_int.mlb Checker_int.sml UPPAAL_Model_Checker_int.sml
	mlton -output munta_int munta_int.mlb
	chmod +x munta_int

munta_ocaml: Checker.ml UPPAAL_Model_Checker.ml
	ocamlfind ocamlopt -package zarith -package angstrom -linkpkg nums.cmxa -linkpkg UPPAAL_Model_Checker.ml -linkpkg Checker.ml -o munta_ocaml
	chmod +x munta_ocaml

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

muntax: muntax.mlb Muntax.sml Simple_Model_Checker.sml
	mlton -output munta muntax.mlb

convert_int: Certificate.ML
	sed -i -e 's/IntInf/Int/g' Certificate.ML

muntac_poly: convert_int
	polyc -o muntac_poly build_muntac.sml

muntac_mlton: convert_int
	mlton -mlb-path-var "MLUNTA_CERT $(MLUNTA_CERT)" -output muntac_mlton muntac.mlb
