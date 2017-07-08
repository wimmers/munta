theory More_List
  imports Main
begin

lemma list_all2_op_map_iff:
  "list_all2 (\<lambda> a b. b = f a) xs ys \<longleftrightarrow> map f xs = ys"
  unfolding list_all2_iff
  proof (induction xs arbitrary: ys)
    case Nil
    then show ?case by auto
  next
    case (Cons a xs ys)
    then show ?case by (cases ys) auto
  qed

lemma list_all2_last:
  "R (last xs) (last ys)" if "list_all2 R xs ys" "xs \<noteq> []"
  using that
  unfolding list_all2_iff
  proof (induction xs arbitrary: ys)
    case Nil
    then show ?case by simp
  next
    case (Cons a xs ys)
    then show ?case by (cases ys) auto
  qed

lemma list_all2_set1:
  "\<forall>x\<in>set xs. \<exists>xa\<in>set as. P x xa" if "list_all2 P xs as"
  using that
proof (induction xs arbitrary: as)
  case Nil
  then show ?case by auto
next
  case (Cons a xs as)
  then show ?case by (cases as) auto
qed

lemma list_all2_swap:
  "list_all2 P xs ys \<longleftrightarrow> list_all2 (\<lambda> x y. P y x) ys xs"
  unfolding list_all2_iff by (fastforce simp: in_set_zip)+

lemma list_all2_set2:
  "\<forall>x\<in>set as. \<exists>xa\<in>set xs. P xa x" if "list_all2 P xs as"
  using that by - (rule list_all2_set1, subst (asm) list_all2_swap)

(* XXX Duplication with Floyd_Warshall.thy *)
lemma distinct_length_le:"finite s \<Longrightarrow> set xs \<subseteq> s \<Longrightarrow> distinct xs \<Longrightarrow> length xs \<le> card s"
  by (metis card_mono distinct_card)

end (* Theory *)