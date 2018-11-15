theory Simple_Network_Language_Export_Code
  imports Simple_Network_Language_Renaming
begin

lemma (in Simple_Network_Impl_nat_defs) bounded_s\<^sub>0_iff:
  "bounded bounds (map_of s\<^sub>0) \<longleftrightarrow> bounded (map_of bounds') (map_of s\<^sub>0)"
  unfolding bounds_def snd_conv ..

lemmas [code] =
  Simple_Network_Impl_nat_ceiling_start_state_def
  Simple_Network_Impl_nat_ceiling_start_state_axioms_def[
    unfolded Simple_Network_Impl_nat_defs.bounded_s\<^sub>0_iff]
  Simple_Network_Impl_nat_def

lemmas [code_unfold] = bounded_def dom_map_of_conv_image_fst

export_code Simple_Network_Impl_nat_ceiling_start_state_axioms

export_code precond_mc in SML module_name Test

end