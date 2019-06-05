theory Simple_Network_Language_Certificate_Checking
  imports
    "../Extract_Certificate"
    "../Normalized_Zone_Semantics_Certification_Impl"
    Simple_Network_Language_Export_Code
    "../library/Trace_Timing"
begin

no_notation test_bit (infixl "!!" 100)

paragraph \<open>Splitters\<close>

context
  fixes f :: "'a \<Rightarrow> nat" and width :: nat
begin

fun split_size :: "nat \<Rightarrow> 'a list \<Rightarrow> 'a list \<Rightarrow> 'a list list" where
  "split_size _ acc [] = [acc]"
| "split_size n acc (x # xs) =
   (let k = f x in if n < width then split_size (n + k) (x # acc) xs else acc # split_size k [x] xs)"

lemma split_size_full_split:
  "(\<Union>x \<in> set (split_size n acc xs). set x) = set xs \<union> set acc"
  by (induction n acc xs rule: split_size.induct) auto

end

definition split_eq_width :: "nat \<Rightarrow> 'a list \<Rightarrow> 'a list list" where
  "split_eq_width n \<equiv> split_size (\<lambda>_. 1 :: nat) n 0 []"

lemma list_all2_split_size_1:
  assumes "list_all2 R xs ys" "list_all2 R acc acc'"
  shows "list_all2 (list_all2 R)
    (split_size (\<lambda>_. 1 :: nat) k n acc xs) (split_size (\<lambda>_. 1 :: nat) k n acc' ys)"
  using assms by (induction arbitrary: acc acc' n rule: list_all2_induct) auto


thm list_all2_induct
term zip

fun zip2 where
  "zip2 [] [] = []"
| "zip2 [] xs = []"
| "zip2 ys [] = []"
| "zip2 (x # xs) (y # ys) = (x, y) # zip2 xs ys"

thm zip2.induct

lemma length_hd_split_size_mono:
  "length (hd (split_size f k n acc xs)) \<ge> length acc"
  apply (induction xs arbitrary: acc n)
   apply auto
  apply (rule order.trans[rotated])
   apply rprems
  apply simp
  done

lemma split_size_non_empty[simp]:
  "split_size f k n acc xs = [] \<longleftrightarrow> False"
  by (induction xs arbitrary: acc n) auto

lemma list_all2_split_size_2:
  assumes "length acc = length acc'"
  shows
  "list_all2 (list_all2 R)
    (split_size (\<lambda>_. 1 :: nat) k n acc xs) (split_size (\<lambda>_. 1 :: nat) k n acc' ys)
\<longleftrightarrow> list_all2 R xs ys \<and> list_all2 R acc acc'"
  using assms
proof (induction xs ys arbitrary: acc acc' n rule: zip2.induct)
  case (2 y ys)
  { assume A: "list_all2 (list_all2 R) [acc] (split_size (\<lambda>_. Suc 0) k (Suc n) (y # acc') ys)"
    then obtain x where "split_size (\<lambda>_. Suc 0) k (Suc n) (y # acc') ys = [x]"
      by (cases "split_size (\<lambda>_. Suc 0) k (Suc n) (y # acc') ys") auto
    with length_hd_split_size_mono[of "y # acc'" "(\<lambda>_. Suc 0)" k "Suc n" ys] have
      "length x \<ge> length (y # acc')"
      by auto
    with A \<open>_ = [x]\<close> \<open>length acc = length acc'\<close> have False
      by (auto dest: list_all2_lengthD)
  }
  with 2 show ?case
    by clarsimp
next
  case (3 y ys)
  { assume A: "list_all2 (list_all2 R) (split_size (\<lambda>_. Suc 0) k (Suc n) (y # acc) ys) [acc']"
    then obtain x where "split_size (\<lambda>_. Suc 0) k (Suc n) (y # acc) ys = [x]"
      by (cases "split_size (\<lambda>_. Suc 0) k (Suc n) (y # acc) ys") auto
    with length_hd_split_size_mono[of "y # acc" "(\<lambda>_. Suc 0)" k "Suc n" ys] have
      "length x \<ge> length (y # acc)"
      by auto
    with A \<open>_ = [x]\<close> \<open>length acc = length acc'\<close> have False
      by (auto dest: list_all2_lengthD)
  }
  with 3 show ?case
    by clarsimp
qed auto

lemma list_all2_split_eq_width:
  shows "list_all2 R xs ys \<longleftrightarrow> list_all2 (list_all2 R) (split_eq_width k xs) (split_eq_width k ys)"
  unfolding split_eq_width_def by (subst list_all2_split_size_2; simp)

lemma length_split_size_1:
  "sum_list (map length (split_size (\<lambda>_. 1 :: nat) k n acc xs)) = length xs + length acc"
  by (induction xs arbitrary: acc n) auto

lemma length_sum_list:
  "sum_list (map length (split_eq_width k xs)) = length xs"
  unfolding split_eq_width_def by (subst length_split_size_1; simp)

definition split_k :: "nat \<Rightarrow> 'a list \<Rightarrow> 'a list list" where
  "split_k k xs \<equiv> let
    width = length xs div k;
    width = (if length xs mod k = 0 then width else width + 1)
  in split_eq_width width xs"

lemma length_hd_split_size:
  "length (hd (split_size (\<lambda>_. 1 :: nat) k n acc xs))
  = (if n + length xs < k then n + length xs else max k n)" if "length acc = n"
  using that by (induction xs arbitrary: n acc) auto

lemma length_hd_split_eq_width:
  "length (hd (split_eq_width width xs)) = (if length xs < width then length xs else width)"
  unfolding split_eq_width_def by (subst length_hd_split_size; simp)

lemma list_all2_split_k:
  "list_all2 R xs ys \<longleftrightarrow> list_all2 (list_all2 R) (split_k k xs) (split_k k ys)"
proof (cases "length xs = length ys")
  case True
  show ?thesis
    unfolding split_k_def Let_def True by (rule list_all2_split_eq_width)
next
  case False
  { assume "list_all2 (list_all2 R) (split_k k xs) (split_k k ys)"
    then have "list_all2 R (concat (split_k k xs)) (concat (split_k k ys))"
      by (meson concat_transfer rel_funD)
    then have "length (concat (split_k k xs)) = length (concat (split_k k ys))"
      by (rule list_all2_lengthD)
    then have "length xs = length ys"
      unfolding split_k_def by (simp add: length_concat length_sum_list)
  }
  with False show ?thesis
    by (auto dest: list_all2_lengthD)
qed

definition split_k' :: "nat \<Rightarrow> ('a \<times> 'b list) list \<Rightarrow> 'a list list" where
  "split_k' k xs \<equiv> let
    width = sum_list (map (length o snd) xs) div k;
    width = (if length xs mod k = 0 then width else width + 1)
  in map (map fst) (split_size (length o snd) width 0 [] xs)"

lemma split_eq_width_full_split:
  "set xs = (\<Union>x \<in> set (split_eq_width n xs). set x)"
  unfolding split_eq_width_def by (auto simp add: split_size_full_split)

lemma split_k_full_split:
  "set xs = (\<Union>x \<in> set (split_k n xs). set x)"
  unfolding split_k_def by (simp add: split_eq_width_full_split)

lemma split_k'_full_split:
  "fst ` set xs = (\<Union>x \<in> set (split_k' n xs). set x)"
  unfolding split_k'_def by (simp add: split_size_full_split image_UN[symmetric])



(* XXX Merge proof with Ex_ev *)
lemma (in Graph_Defs) Ex_ev_reaches:
  "\<exists> y. x \<rightarrow>* y \<and> \<phi> y" if "Ex_ev \<phi> x"
  using that unfolding Ex_ev_def
proof safe
  fix xs assume prems: "run (x ## xs)" "ev (holds \<phi>) (x ## xs)"
  show "\<exists>y. x \<rightarrow>* y \<and> \<phi> y"
  proof (cases "\<phi> x")
    case True
    then show ?thesis
      by auto
  next
    case False
    with prems obtain y ys zs where
      "\<phi> y" "xs = ys @- y ## zs" "y \<notin> set ys"
      unfolding ev_holds_sset by (auto elim!:split_stream_first)
    with prems have "steps (x # ys @ [y])"
      by (auto intro: run_decomp[THEN conjunct1]) (* XXX *)
    with \<open>\<phi> y\<close> show ?thesis
      including graph_automation by (auto 4 3)
  qed
qed

text \<open>More debugging auxiliaries\<close>

concrete_definition (in -) M_table
  uses Reachability_Problem_Impl_Precise.M_table_def

definition
  "check_nonneg n M \<equiv> imp_for 0 (n + 1) Heap_Monad.return
    (\<lambda>xc \<sigma>. mtx_get (Suc n) M (0, xc) \<bind> (\<lambda>x'e. Heap_Monad.return (x'e \<le> Le 0))) True"  

definition
  "check_diag_nonpos n M \<equiv> imp_for 0 (n + 1) Heap_Monad.return
    (\<lambda>xc \<sigma>. mtx_get (Suc n) M (xc, xc) \<bind> (\<lambda>x'd. Heap_Monad.return (x'd \<le> Le 0))) True"


text \<open>Complete DBM printing\<close>

context
  fixes n :: nat
  fixes show_clock :: "nat \<Rightarrow> string"
    and show_num :: "'a :: {linordered_ab_group_add,heap} \<Rightarrow> string"
  notes [id_rules] = itypeI[of n "TYPE (nat)"]
    and [sepref_import_param] = IdI[of n]
begin

definition
  "make_string' e i j \<equiv>
    let
      i = (if i > 0 then show_clock i else ''0'');
      j = (if j > 0 then show_clock j else ''0'')
    in
    case e of
      DBMEntry.Le a \<Rightarrow> i @ '' - '' @ j @ '' <= '' @ show_num a
    | DBMEntry.Lt a \<Rightarrow> i @ '' - '' @ j @ '' < '' @ show_num a
    | _ \<Rightarrow> i @ '' - '' @ j @ '' < inf''"

definition
  "dbm_list_to_string' xs \<equiv>
  (concat o intersperse '', '' o rev o snd o snd) $ fold (\<lambda>e (i, j, acc).
    let
      s = make_string' e i j;
      j = (j + 1) mod (n + 1);
      i = (if j = 0 then i + 1 else i)
    in (i, j, s # acc)
  ) xs (0, 0, [])"

lemma [sepref_import_param]:
  "(dbm_list_to_string', PR_CONST dbm_list_to_string') \<in> \<langle>Id\<rangle>list_rel \<rightarrow> \<langle>Id\<rangle>list_rel"
  by simp

definition show_dbm' where
  "show_dbm' M \<equiv> PR_CONST dbm_list_to_string' (dbm_to_list n M)"

sepref_register "PR_CONST dbm_list_to_string'"

lemmas [sepref_fr_rules] = dbm_to_list_impl.refine

sepref_definition show_dbm_impl_all is
  "Refine_Basic.RETURN o show_dbm'" :: "(mtx_assn n)\<^sup>k \<rightarrow>\<^sub>a list_assn id_assn"
  unfolding show_dbm'_def by sepref

end (* Context for show functions and importing n *)

definition
  "abstr_repair_impl m \<equiv>
  \<lambda>ai. imp_nfoldli ai (\<lambda>\<sigma>. Heap_Monad.return True)
      (\<lambda>ai bi. abstra_upd_impl m ai bi \<bind> (\<lambda>x'. repair_pair_impl m x' 0 (constraint_clk ai)))"

definition E_op_impl ::
  "nat \<Rightarrow> (nat, int) acconstraint list \<Rightarrow> nat list \<Rightarrow> _"
  where
  "E_op_impl m l_inv r g l'_inv M \<equiv>
do {
   M1 \<leftarrow> up_canonical_upd_impl m M m;
   M2 \<leftarrow> abstr_repair_impl m l_inv M1;
   is_empty1 \<leftarrow> check_diag_impl m M2;
   M3 \<leftarrow> (if is_empty1 then mtx_set (Suc m) M2 (0, 0) (Lt 0) else abstr_repair_impl m g M2);
   is_empty3 \<leftarrow> check_diag_impl m M3;
   if is_empty3 then
     mtx_set (Suc m) M3 (0, 0) (Lt 0)
   else do {
     M4 \<leftarrow>
       imp_nfoldli r (\<lambda>\<sigma>. Heap_Monad.return True) (\<lambda>xc \<sigma>. reset_canonical_upd_impl m \<sigma> m xc 0) M3;
     abstr_repair_impl m l'_inv M4
   }
}"



paragraph \<open>Full Monomorphization of @{term E_op_impl}\<close>

definition min_int :: "int \<Rightarrow> int \<Rightarrow> int" where
  "min_int x y \<equiv> if x \<le> y then x else y"

named_theorems int_folds

lemma min_int_fold[int_folds]:
  "min = min_int"
  unfolding min_int_def min_def ..

fun min_int_entry :: "int DBMEntry \<Rightarrow> int DBMEntry \<Rightarrow> int DBMEntry" where
  "min_int_entry (Lt x) (Lt y) = (if x \<le> y then Lt x else Lt y)"
| "min_int_entry (Lt x) (Le y) = (if x \<le> y then Lt x else Le y)"
| "min_int_entry (Le x) (Lt y) = (if x < y then Le x else Lt y)"
| "min_int_entry (Le x) (Le y) = (if x \<le> y then Le x else Le y)"
| "min_int_entry \<infinity> x = x"
| "min_int_entry x \<infinity> = x"


export_code min_int_entry in SML

lemma min_int_entry[int_folds]:
  "min = min_int_entry"
  apply (intro ext)
  subgoal for a b
    by (cases a; cases b; simp add: dbm_entry_simps)
  done

fun dbm_le_int :: "int DBMEntry \<Rightarrow> int DBMEntry \<Rightarrow> bool" where
  "dbm_le_int (Lt a) (Lt b) \<longleftrightarrow> a \<le> b"
| "dbm_le_int (Lt a) (Le b) \<longleftrightarrow> a \<le> b"
| "dbm_le_int (Le a) (Lt b) \<longleftrightarrow> a < b"
| "dbm_le_int (Le a) (Le b) \<longleftrightarrow> a \<le> b"
| "dbm_le_int _ \<infinity> \<longleftrightarrow> True"
| "dbm_le_int _ _ \<longleftrightarrow> False"

lemma dbm_le_dbm_le_int[int_folds]:
  "dbm_le = dbm_le_int"
  apply (intro ext)
  subgoal for a b
    by (cases a; cases b; auto simp: dbm_le_def)
  done

fun dbm_lt_int :: "int DBMEntry \<Rightarrow> int DBMEntry \<Rightarrow> bool"
  where
  "dbm_lt_int (Le a) (Le b) \<longleftrightarrow> a < b" |
  "dbm_lt_int (Le a) (Lt b) \<longleftrightarrow> a < b" |
  "dbm_lt_int (Lt a) (Le b) \<longleftrightarrow> a \<le> b" |
  "dbm_lt_int (Lt a) (Lt b) \<longleftrightarrow> a < b" |
  "dbm_lt_int \<infinity> _ = False" |
  "dbm_lt_int _ \<infinity> = True"

lemma dbm_lt_dbm_lt_int[int_folds]:
  "dbm_lt = dbm_lt_int"
  apply (intro ext)
  subgoal for a b
    by (cases a; cases b; auto)
  done

definition [symmetric, int_folds]:
  "dbm_lt_0 x \<equiv> x < (Le (0 :: int))"

lemmas [int_folds] = dbm_lt_0_def[unfolded DBM.less]

lemma dbm_lt_0_code_simps [code]:
  "dbm_lt_0 (Le x) \<longleftrightarrow> x < 0"
  "dbm_lt_0 (Lt x) \<longleftrightarrow> x \<le> 0"
  "dbm_lt_0 \<infinity> = False"
  unfolding dbm_lt_0_def[symmetric] DBM.less dbm_lt_dbm_lt_int by simp+


definition abstra_upd_impl_int
  :: "nat \<Rightarrow> (nat, int) acconstraint \<Rightarrow> int DBMEntry Heap.array \<Rightarrow> int DBMEntry Heap.array Heap"
  where [symmetric, int_folds]:
    "abstra_upd_impl_int = abstra_upd_impl"

schematic_goal abstra_upd_impl_int_code[code]:
  "abstra_upd_impl_int \<equiv> ?i"
  unfolding abstra_upd_impl_int_def[symmetric] abstra_upd_impl_def
  unfolding int_folds
  .

definition fw_upd_impl_int
  :: "nat \<Rightarrow> int DBMEntry Heap.array \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> int DBMEntry Heap.array Heap"
  where [symmetric, int_folds]:
  "fw_upd_impl_int = fw_upd_impl"

lemmas [int_folds] = DBM.add dbm_add_int

schematic_goal fw_upd_impl_int_code [code]:
  "fw_upd_impl_int \<equiv> ?i"
  unfolding fw_upd_impl_int_def[symmetric] fw_upd_impl_def
  unfolding int_folds
  .

definition fwi_impl_int
  :: "nat \<Rightarrow> int DBMEntry Heap.array \<Rightarrow> nat \<Rightarrow> int DBMEntry Heap.array Heap"
  where [symmetric, int_folds]:
  "fwi_impl_int = fwi_impl"

schematic_goal fwi_impl_int_code [code]:
  "fwi_impl_int \<equiv> ?i"
  unfolding fwi_impl_int_def[symmetric] fwi_impl_def unfolding int_folds .

definition fw_impl_int
  :: "nat \<Rightarrow> int DBMEntry Heap.array \<Rightarrow> int DBMEntry Heap.array Heap"
  where [symmetric, int_folds]:
  "fw_impl_int = fw_impl"

schematic_goal fw_impl_int_code [code]:
  "fw_impl_int \<equiv> ?i"
  unfolding fw_impl_int_def[symmetric] fw_impl_def unfolding int_folds .

definition repair_pair_impl_int
  :: "nat \<Rightarrow> int DBMEntry Heap.array \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> int DBMEntry Heap.array Heap"
  where [symmetric, int_folds]:
  "repair_pair_impl_int \<equiv> repair_pair_impl"

schematic_goal repair_pair_impl_int_code[code]:
  "repair_pair_impl_int \<equiv> ?i"
  unfolding repair_pair_impl_int_def[symmetric] repair_pair_impl_def
  unfolding int_folds
  .

definition abstr_repair_impl_int
  :: "nat \<Rightarrow> (nat, int) acconstraint list \<Rightarrow> int DBMEntry Heap.array \<Rightarrow> int DBMEntry Heap.array Heap"
  where [symmetric, int_folds]:
  "abstr_repair_impl_int = abstr_repair_impl"

schematic_goal abstr_repair_impl_int_code[code]:
  "abstr_repair_impl_int \<equiv> ?i"
  unfolding abstr_repair_impl_int_def[symmetric] abstr_repair_impl_def
  unfolding int_folds
  .

definition check_diag_impl_int
  :: "nat \<Rightarrow> int DBMEntry Heap.array \<Rightarrow> bool Heap"
  where [symmetric, int_folds]:
    "check_diag_impl_int = check_diag_impl"

schematic_goal check_diag_impl_int_code[code]:
  "check_diag_impl_int \<equiv> ?i"
  unfolding check_diag_impl_int_def[symmetric] check_diag_impl_def
  unfolding int_folds
  .

definition check_diag_impl'_int
  :: "nat \<Rightarrow> nat \<Rightarrow> int DBMEntry Heap.array \<Rightarrow> bool Heap"
  where [symmetric, int_folds]:
    "check_diag_impl'_int = check_diag_impl'"

schematic_goal check_diag_impl'_int_code[code]:
  "check_diag_impl'_int \<equiv> ?i"
  unfolding check_diag_impl'_int_def[symmetric] check_diag_impl'_def
  unfolding int_folds
  .

definition reset_canonical_upd_impl_int
  :: "nat \<Rightarrow> int DBMEntry Heap.array \<Rightarrow> _"
  where [symmetric, int_folds]:
    "reset_canonical_upd_impl_int = reset_canonical_upd_impl"

schematic_goal reset_canonical_upd_impl_int_code[code]:
  "reset_canonical_upd_impl_int \<equiv> ?i"
  unfolding reset_canonical_upd_impl_int_def[symmetric] reset_canonical_upd_impl_def
  unfolding int_folds
  .

definition up_canonical_upd_impl_int
  :: "nat \<Rightarrow> int DBMEntry Heap.array \<Rightarrow> _"
  where [symmetric, int_folds]:
  "up_canonical_upd_impl_int = up_canonical_upd_impl"

schematic_goal up_canonical_upd_impl_int_code[code]:
  "up_canonical_upd_impl_int \<equiv> ?i"
  unfolding up_canonical_upd_impl_int_def[symmetric] up_canonical_upd_impl_def
  .

schematic_goal E_op_impl_code[code]:
  "E_op_impl \<equiv> ?i"
  unfolding E_op_impl_def
  unfolding int_folds
  .

definition free_impl_int :: "nat \<Rightarrow> int DBMEntry Heap.array \<Rightarrow> _"
  where [symmetric, int_folds]:
    "free_impl_int = free_impl"

schematic_goal free_impl_int_code[code]:
  "free_impl_int \<equiv> ?i"
  unfolding free_impl_int_def[symmetric] free_impl_def
  unfolding int_folds
  .

definition down_impl_int :: "nat \<Rightarrow> int DBMEntry Heap.array \<Rightarrow> _"
  where [symmetric, int_folds]:
    "down_impl_int = down_impl"

schematic_goal down_impl_int_code[code]:
  "down_impl_int \<equiv> ?i"
  unfolding down_impl_int_def[symmetric] down_impl_def
  unfolding int_folds
  .

fun neg_dbm_entry_int where
  "neg_dbm_entry_int (Le (a :: int)) = Lt (-a)" |
  "neg_dbm_entry_int (Lt a) = Le (-a)" |
  "neg_dbm_entry_int DBMEntry.INF = DBMEntry.INF"

lemma neg_dbm_entry_int_fold [int_folds]:
  "neg_dbm_entry = neg_dbm_entry_int"
  apply (intro ext)
  subgoal for x
    by (cases x; auto)
  done

schematic_goal and_entry_impl_code [code]:
  "and_entry_impl \<equiv> ?impl"
  unfolding and_entry_impl_def unfolding int_folds .

schematic_goal and_entry_repair_impl_code [code]:
  "and_entry_repair_impl \<equiv> ?impl"
  unfolding and_entry_repair_impl_def unfolding int_folds .

definition upd_entry_impl_int :: "_ \<Rightarrow> _ \<Rightarrow> _ \<Rightarrow> int DBMEntry Heap.array \<Rightarrow> _"
  where [symmetric, int_folds]:
    "upd_entry_impl_int = upd_entry_impl"

schematic_goal upd_entry_impl_int_code [code]:
  "upd_entry_impl_int \<equiv> ?i"
  unfolding upd_entry_impl_int_def[symmetric] upd_entry_impl_def unfolding int_folds .

schematic_goal upd_entries_impl_code [code]:
  "upd_entries_impl \<equiv> ?impl"
  unfolding upd_entries_impl_def int_folds .

definition get_entries_impl_int :: "nat \<Rightarrow> int DBMEntry Heap.array \<Rightarrow> _"
  where [symmetric, int_folds]:
    "get_entries_impl_int = get_entries_impl"

schematic_goal get_entries_impl_int_code[code]:
  "get_entries_impl_int \<equiv> ?i"
  unfolding get_entries_impl_int_def[symmetric] get_entries_impl_def unfolding int_folds .

schematic_goal dbm_minus_canonical_impl_code [code]:
  "dbm_minus_canonical_impl \<equiv> ?i"
  unfolding dbm_minus_canonical_impl_def unfolding int_folds .


definition abstr_upd_impl_int
  :: "nat \<Rightarrow> (nat, int) acconstraint list \<Rightarrow> int DBMEntry Heap.array \<Rightarrow> int DBMEntry Heap.array Heap"
  where [symmetric, int_folds]:
    "abstr_upd_impl_int = abstr_upd_impl"

schematic_goal abstr_upd_impl_int_code[code]:
  "abstr_upd_impl_int \<equiv> ?i"
  unfolding abstr_upd_impl_int_def[symmetric] abstr_upd_impl_def unfolding int_folds .


definition abstr_FW_impl_int :: "_ \<Rightarrow> _ \<Rightarrow> int DBMEntry Heap.array \<Rightarrow> _"
  where [symmetric, int_folds]:
    "abstr_FW_impl_int = abstr_FW_impl"

schematic_goal abstr_FW_impl_int_code [code]:
  "abstr_FW_impl_int \<equiv> ?i"
  unfolding abstr_FW_impl_int_def[symmetric] abstr_FW_impl_def unfolding int_folds .



paragraph \<open>Extracting executable implementations\<close>

lemma hfkeep_hfdropI:
  assumes "(fi, f) \<in> A\<^sup>k \<rightarrow>\<^sub>a B"
  shows "(fi, f) \<in> A\<^sup>d \<rightarrow>\<^sub>a B"
  supply [sep_heap_rules] =
    assms[to_hnr, unfolded hn_refine_def, simplified hn_ctxt_def, simplified, rule_format]
  by sepref_to_hoare sep_auto

context Simple_Network_Impl_nat_ceiling_start_state
begin

sublocale impl: Reachability_Problem_Impl_Precise
  where trans_fun = trans_from
  and inv_fun = inv_fun
  (* and F_fun = Fi *)
  and ceiling = k_impl
  and A = prod_ta
  and l\<^sub>0 = l\<^sub>0
  and l\<^sub>0i = l\<^sub>0i
  (* and F = "PR_CONST F" *)
  and n = m
  and k = k_fun
  and trans_impl = trans_impl
  and states' = states'
  and loc_rel = loc_rel
  and f = reach.E_precise_op'
  and op_impl = "PR_CONST impl.E_precise_op'_impl"
  and states_mem_impl = states'_memi
  and F = "\<lambda>(l, _). F l"
  and F1 = "F o fst"
  and F' = "F o fst"
  and F_impl = impl.F_impl
  apply standard
       apply (unfold PR_CONST_def, rule impl.E_precise_op'_impl.refine, rule states'_memi_correct)
  subgoal
    by auto
  subgoal
    apply simp
    done
subgoal
    apply simp
  done
  subgoal
    using impl.F_impl.refine by (intro hfkeep_hfdropI) simp
  done

lemma state_impl_abstract':
  assumes "states'_memi li"
  shows "\<exists>l. (li, l) \<in> loc_rel"
proof -
  obtain Li si where "li = (Li, si)"
    by force
  with state_impl_abstract[of Li si] show ?thesis
    using assms unfolding states'_memi_def states_def by auto
qed

interpretation Bisimulation_Invariant
  "(\<lambda>(l, u) (l', u'). conv_A prod_ta \<turnstile>' \<langle>l, u\<rangle> \<rightarrow> \<langle>l', u'\<rangle>)"
  "(\<lambda>(L, s, u) (L', s', u'). Simple_Network_Language.conv A \<turnstile> \<langle>L, s, u\<rangle> \<rightarrow> \<langle>L', s', u'\<rangle>)"
  "(\<lambda>((L, s), u) (L', s', u'). L = L' \<and> u = u' \<and> s = s')"
  "(\<lambda>((L, s), u). conv.all_prop L s)"
  "(\<lambda>(L, s, u). conv.all_prop L s)"
  apply (rule prod_bisim)
  done (* XXX Why does 'by' not work? *)

lemma unreachability_prod:
  assumes
    "formula = formula.EX \<phi>"
    "(\<nexists>u l' u'. (\<forall>c\<le>m. u c = 0) \<and> conv_A prod_ta \<turnstile>' \<langle>l\<^sub>0, u\<rangle> \<rightarrow>* \<langle>l', u'\<rangle> \<and> PR_CONST F l')"
  shows "\<not> Simple_Network_Language.conv A,(L\<^sub>0, map_of s\<^sub>0, \<lambda>_. 0) \<Turnstile> formula"
proof -
  let ?check = "\<not> B.Ex_ev (\<lambda>(L, s, _). check_sexp \<phi> L (the \<circ> s)) (L\<^sub>0, map_of s\<^sub>0, \<lambda>_. 0)"
  have *: "PR_CONST F l \<longleftrightarrow> (\<lambda>((L, s), _). check_sexp \<phi> L (the o s)) (l, u)"
    for l and u :: "nat \<Rightarrow> real"
    unfolding assms(1) by auto
  have "conv.all_prop L\<^sub>0 (map_of s\<^sub>0)"
    using all_prop_start unfolding conv_all_prop .
  then have
    "?check \<longleftrightarrow> \<not> reach.Ex_ev (\<lambda> ((L, s), _). check_sexp \<phi> L (the o s)) (l\<^sub>0, u\<^sub>0)"
    by (auto intro!: Ex_ev_iff[symmetric, unfolded A_B.equiv'_def])
  also from assms(2) have "\<dots>"
    apply -
    apply standard
    apply (drule reach.Ex_ev_reaches)
    unfolding impl.reaches_steps'[symmetric]
    apply (subst (asm) *)
    apply force
    done
  finally show ?thesis
    using assms unfolding models_def by simp
qed

lemma deadlock_prod:
  "\<not> reach.deadlock (l\<^sub>0, \<lambda>_. 0)
  \<longleftrightarrow> \<not> has_deadlock (Simple_Network_Language.conv A) (L\<^sub>0, map_of s\<^sub>0, \<lambda>_. 0)"
  unfolding has_deadlock_def deadlock_start_iff ..

lemma list_assn_split:
  "list_assn (list_assn impl.location_assn) (split_k num_split L) (split_k num_split Li) =
   list_assn impl.location_assn L Li"
proof -
  have 1: "impl.location_assn = pure (the_pure impl.location_assn)"
    using impl.pure_K by auto
  have "(split_k num_split Li, split_k num_split L) \<in> \<langle>\<langle>the_pure impl.location_assn\<rangle>list_rel\<rangle>list_rel
  \<longleftrightarrow> (Li, L) \<in> \<langle>the_pure impl.location_assn\<rangle>list_rel"
    unfolding list_rel_def by (auto simp: list_all2_split_k[symmetric])
  then show ?thesis
    apply (subst (2) 1, subst 1)
    unfolding list_assn_pure_conv unfolding pure_def by auto
qed

theorem unreachability_checker_hnr:
  assumes "\<And>li. P_loc li \<Longrightarrow> states'_memi li"
    and "list_all (\<lambda>x. P_loc x \<and> states'_memi x) L_list"
    and "list_all (\<lambda>(l, y). list_all (\<lambda>M. length M = Suc m * Suc m) y) M_list"
    and "fst ` set M_list = set L_list"
    and "formula = formula.EX \<phi>"
  shows "(
  uncurry0 (impl.unreachability_checker L_list M_list (split_k num_split)),
  uncurry0 (SPEC (\<lambda>r. r \<longrightarrow>
    \<not> Simple_Network_Language.conv A,(L\<^sub>0, map_of s\<^sub>0, \<lambda>_. 0) \<Turnstile> formula)))
  \<in> unit_assn\<^sup>k \<rightarrow>\<^sub>a bool_assn"
proof -
  define checker where "checker \<equiv> impl.unreachability_checker L_list M_list"
  from assms(4) have "fst ` set M_list \<subseteq> set L_list"
    by blast
  note [sep_heap_rules] =
    impl.unreachability_checker_hnr[
      OF state_impl_abstract',
      OF assms(1,2) this assms(3) split_k_full_split list_assn_split
        impl.L_dom_M_eqI[OF state_impl_abstract', OF assms(1,2) this assms(3,4)],
      to_hnr, unfolded hn_refine_def, rule_format, folded checker_def
    ]
  show ?thesis
    unfolding checker_def[symmetric] using unreachability_prod[OF assms(5)]
    by sepref_to_hoare (sep_auto simp: pure_def)
qed

theorem unreachability_checker2_refine:
  assumes "\<And>li. P_loc li \<Longrightarrow> states'_memi li"
    and "list_all (\<lambda>x. P_loc x \<and> states'_memi x) L_list"
    and "list_all (\<lambda>(l, y). list_all (\<lambda>M. length M = Suc m * Suc m) y) M_list"
    and "fst ` set M_list = set L_list"
    and "formula = formula.EX \<phi>"
  shows "
  impl.unreachability_checker2 L_list M_list (split_k num_split) \<longrightarrow>
    \<not> Simple_Network_Language.conv A,(L\<^sub>0, map_of s\<^sub>0, \<lambda>_. 0) \<Turnstile> formula"
  using impl.unreachability_checker2_refine[OF state_impl_abstract',
      OF assms(1,2) assms(4)[THEN equalityD1] assms(3) split_k_full_split list_assn_split assms(4)
      ]
    unreachability_prod[OF assms(5)]
  by auto

theorem unreachability_checker3_refine:
  assumes "\<And>li. P_loc li \<Longrightarrow> states'_memi li"
    and "list_all (\<lambda>x. P_loc x \<and> states'_memi x) L_list"
    and "list_all (\<lambda>(l, y). list_all (\<lambda>M. length M = Suc m * Suc m) y) M_list"
    and "fst ` set M_list = set L_list"
    and "formula = formula.EX \<phi>"
  shows "
  impl.certify_unreachable_pure L_list M_list (split_k' num_split M_list) \<longrightarrow>
    \<not> Simple_Network_Language.conv A,(L\<^sub>0, map_of s\<^sub>0, \<lambda>_. 0) \<Turnstile> formula"
  using impl.certify_unreachable_pure_refine[
      OF state_impl_abstract', OF assms(1,2) assms(4)[THEN equalityD1] assms(3)
         split_k'_full_split[of M_list, unfolded assms(4)] assms(4)
      ]
    unreachability_prod[OF assms(5)]
  by auto

lemma abstr_repair_impl_refine:
  "impl.abstr_repair_impl = abstr_repair_impl m"
  unfolding abstr_repair_impl_def impl.abstr_repair_impl_def  impl.abstra_repair_impl_def ..

lemma E_op_impl_refine:
  "impl.E_precise_op'_impl l r g l' M = E_op_impl m (inv_fun l) r g (inv_fun l') M"
  unfolding impl.E_precise_op'_impl_def E_op_impl_def abstr_repair_impl_refine ..

definition
  "succs1 n_ps invs \<equiv>
  let
    inv_fun = \<lambda>(L, a). concat (map (\<lambda>i. invs !! i !! (L ! i)) [0..<n_ps]);
    E_op_impl = (\<lambda>l r g l' M. E_op_impl m (inv_fun l) r g (inv_fun l') M)
  in (\<lambda>L_s M.
    if M = [] then Heap_Monad.return []
    else imp_nfoldli (trans_impl L_s) (\<lambda>\<sigma>. Heap_Monad.return True)
      (\<lambda>c \<sigma>. case c of (g, a1a, r, L_s') \<Rightarrow> do {
        M \<leftarrow> heap_map amtx_copy M;
        Ms \<leftarrow> imp_nfoldli M (\<lambda>\<sigma>. Heap_Monad.return True)
          (\<lambda>xb \<sigma>. do {
            x'c \<leftarrow> E_op_impl L_s r g L_s' xb;
            x'e \<leftarrow> check_diag_impl m x'c;
            Heap_Monad.return (if x'e then \<sigma> else op_list_prepend x'c \<sigma>)
          }) [];
        Heap_Monad.return (op_list_prepend (L_s', Ms) \<sigma>)
      })
    [])" for n_ps :: "nat" and invs :: "(nat, int) acconstraint list iarray iarray"

lemma succs1_refine:
  "impl.succs_precise'_impl = succs1 n_ps invs2"
  unfolding impl.succs_precise'_impl_def impl.succs_precise_inner_impl_def
  unfolding succs1_def Let_def PR_CONST_def E_op_impl_refine
  unfolding inv_fun_alt_def ..

schematic_goal trans_impl_alt_def:
  "trans_impl \<equiv> ?impl"
  unfolding trans_impl_def
  apply (abstract_let int_trans_impl int_trans_impl)
  apply (abstract_let bin_trans_from_impl bin_trans_impl)
  apply (abstract_let broad_trans_from_impl broad_trans_impl)
  unfolding int_trans_impl_def bin_trans_from_impl_def broad_trans_from_impl_def
  apply (abstract_let trans_in_broad_grouped trans_in_broad_grouped)
  apply (abstract_let trans_out_broad_grouped trans_out_broad_grouped)
  apply (abstract_let trans_in_map trans_in_map)
  apply (abstract_let trans_out_map trans_out_map)
  apply (abstract_let int_trans_from_all_impl int_trans_from_all_impl)
  unfolding int_trans_from_all_impl_def
  apply (abstract_let int_trans_from_vec_impl int_trans_from_vec_impl)
  unfolding int_trans_from_vec_impl_def
  apply (abstract_let int_trans_from_loc_impl int_trans_from_loc_impl)
  unfolding int_trans_from_loc_impl_def
  apply (abstract_let trans_i_map trans_i_map)
  unfolding trans_out_broad_grouped_def trans_out_broad_map_def
  unfolding trans_in_broad_grouped_def trans_in_broad_map_def
  unfolding trans_in_map_def trans_out_map_def
  unfolding trans_i_map_def
  apply (abstract_let trans_map trans_map)
  .

schematic_goal succs1_alt_def:
  "succs1 \<equiv> ?impl"
  unfolding succs1_def
  apply (abstract_let trans_impl trans_impl)
  unfolding trans_impl_alt_def
  .

schematic_goal succs_impl_alt_def:
  "impl.succs_precise'_impl \<equiv> ?impl"
  unfolding impl.succs_precise'_impl_def impl.succs_precise_inner_impl_def
  apply (abstract_let impl.E_precise_op'_impl E_op_impl)
  unfolding impl.E_precise_op'_impl_def fw_impl'_int
  apply (abstract_let trans_impl trans_impl)
  unfolding trans_impl_def
  apply (abstract_let int_trans_impl int_trans_impl)
  apply (abstract_let bin_trans_from_impl bin_trans_impl)
  apply (abstract_let broad_trans_from_impl broad_trans_impl)
  unfolding int_trans_impl_def bin_trans_from_impl_def broad_trans_from_impl_def
  apply (abstract_let trans_in_broad_grouped trans_in_broad_grouped)
  apply (abstract_let trans_out_broad_grouped trans_out_broad_grouped)
  apply (abstract_let trans_in_map trans_in_map)
  apply (abstract_let trans_out_map trans_out_map)
  apply (abstract_let int_trans_from_all_impl int_trans_from_all_impl)
  unfolding int_trans_from_all_impl_def
  apply (abstract_let int_trans_from_vec_impl int_trans_from_vec_impl)
  unfolding int_trans_from_vec_impl_def
  apply (abstract_let int_trans_from_loc_impl int_trans_from_loc_impl)
  unfolding int_trans_from_loc_impl_def
  apply (abstract_let trans_i_map trans_i_map)
  unfolding trans_out_broad_grouped_def trans_out_broad_map_def
  unfolding trans_in_broad_grouped_def trans_in_broad_map_def
  unfolding trans_in_map_def trans_out_map_def
  unfolding trans_i_map_def
  apply (abstract_let trans_map trans_map)
  apply (abstract_let "inv_fun :: nat list \<times> int list \<Rightarrow> _" inv_fun)
  unfolding inv_fun_alt_def
  apply (abstract_let invs2 invs)
  unfolding invs2_def
  apply (abstract_let n_ps n_ps)
  by (rule Pure.reflexive)

end

concrete_definition (in -) succs_impl
  uses Simple_Network_Impl_nat_ceiling_start_state.succs1_alt_def

context Simple_Network_Impl_nat_ceiling_start_state
begin

context
  fixes L_list and M_list :: "((nat list \<times> int list) \<times> int DBMEntry list list) list"
  assumes assms:
    "list_all states'_memi L_list"
    "fst ` set M_list \<subseteq> set L_list"
    "list_all (\<lambda>(l, y). list_all (\<lambda>M. length M = Suc m * Suc m) y) M_list"
begin

private lemma A:
  "list_all (\<lambda>x. states'_memi x \<and> states'_memi x) L_list"
  using assms by simp

lemma unreachability_checker_def:
  "impl.unreachability_checker L_list M_list (split_k num_split) \<equiv>
   let Fi = impl.F_impl; Pi = impl.P_impl; copyi = amtx_copy; Lei = dbm_subset_impl m;
       l\<^sub>0i = Heap_Monad.return l\<^sub>0i; s\<^sub>0i = impl.init_dbm_impl; succsi = impl.succs_precise'_impl
   in do {
    let _ = start_timer ();
    M_table \<leftarrow> impl.M_table M_list;
    let _ = save_time STR ''Time for loading certificate'';
    r \<leftarrow> certify_unreachable_impl_inner
      Fi Pi copyi Lei l\<^sub>0i s\<^sub>0i succsi (split_k num_split) L_list M_table;
    Heap_Monad.return r
  }"
  by (subst impl.unreachability_checker_alt_def[OF
        state_impl_abstract', OF _ A assms(2,3) split_k_full_split list_assn_split];
      simp)

schematic_goal unreachability_checker_alt_def:
  "impl.unreachability_checker L_list M_list (split_k num_split) \<equiv> ?x"
  apply (subst unreachability_checker_def)
  apply (subst impl.M_table_def[OF state_impl_abstract', of states'_memi, OF _ A assms(2,3)])
   apply assumption
  unfolding impl.F_impl_def impl.P_impl_def
  apply (abstract_let states'_memi check_states)
  unfolding states'_memi_def states_mem_compute'
  apply (abstract_let "map states_i [0..<n_ps]" states_i)
  unfolding succs_impl_alt_def
  unfolding k_impl_alt_def k_i_def
  (* The following are just to unfold things that should have been defined in a defs locale *)
  unfolding impl.E_op''_impl_def impl.abstr_repair_impl_def impl.abstra_repair_impl_def
  unfolding
    impl.start_inv_check_impl_def impl.unbounded_dbm_impl_def
    impl.unbounded_dbm'_def
  unfolding impl.init_dbm_impl_def impl.a\<^sub>0_impl_def
  unfolding impl.subsumes_impl_def
  unfolding impl.emptiness_check_impl_def
  unfolding impl.state_copy_impl_def
  by (rule Pure.reflexive)

definition no_deadlock_certifier where
  "no_deadlock_certifier \<equiv>
  Reachability_Problem_Impl_Precise.unreachability_checker
    m trans_impl l\<^sub>0i (PR_CONST impl.E_precise_op'_impl)
    states'_memi (\<lambda>(l, M). impl.check_deadlock_impl l M \<bind> (\<lambda>r. Heap_Monad.return (\<not> r)))"

lemma no_deadlock_certifier_alt_def1:
  "no_deadlock_certifier L_list M_list (split_k num_split) \<equiv>
   let
      Fi = (\<lambda>(l, M). impl.check_deadlock_impl l M \<bind> (\<lambda>r. Heap_Monad.return (\<not> r)));
      Pi = impl.P_impl; copyi = amtx_copy; Lei = dbm_subset_impl m;
      l\<^sub>0i = Heap_Monad.return l\<^sub>0i; s\<^sub>0i = impl.init_dbm_impl;
      succsi = impl.succs_precise'_impl
   in do {
    let _ = start_timer ();
    M_table \<leftarrow> impl.M_table M_list;
    let _ = save_time STR ''Time for loading certificate'';
    r \<leftarrow> certify_unreachable_impl_inner Fi Pi copyi Lei l\<^sub>0i s\<^sub>0i succsi (split_k num_split) L_list M_table;
    Heap_Monad.return r
  }"
  unfolding no_deadlock_certifier_def
  by (subst impl.deadlock_unreachability_checker_alt_def[
        OF state_impl_abstract', OF _ A assms(2,3) split_k_full_split list_assn_split
        ];
      simp)

schematic_goal check_deadlock_impl_alt_def:
  "impl.check_deadlock_impl \<equiv> ?impl"
  unfolding impl.check_deadlock_impl_def
  apply (abstract_let trans_impl trans_impl)
  unfolding trans_impl_alt_def
  apply (abstract_let "inv_fun :: nat list \<times> int list \<Rightarrow> _" inv_fun)
  unfolding inv_fun_alt_def
  apply (abstract_let invs2 invs)
  unfolding invs2_def
  apply (abstract_let n_ps n_ps)
  .

schematic_goal no_deadlock_certifier_alt_def:
  "no_deadlock_certifier L_list M_list (split_k num_split) \<equiv> ?x"
  apply (subst no_deadlock_certifier_alt_def1)
  apply (subst impl.M_table_def[OF state_impl_abstract', of states'_memi, OF _ A assms(2,3)])
   apply assumption
  unfolding check_deadlock_impl_alt_def impl.P_impl_def
  apply (abstract_let states'_memi check_states)
  unfolding states'_memi_def states_mem_compute'
  apply (abstract_let "map states_i [0..<n_ps]" states_i)
  unfolding succs_impl_alt_def
  unfolding k_impl_alt_def k_i_def
  (* The following are just to unfold things that should have been defined in a defs locale *)
  unfolding impl.E_op''_impl_def impl.abstr_repair_impl_def impl.abstra_repair_impl_def
  unfolding
    impl.start_inv_check_impl_def impl.unbounded_dbm_impl_def
    impl.unbounded_dbm'_def
  unfolding impl.init_dbm_impl_def impl.a\<^sub>0_impl_def
  unfolding impl.subsumes_impl_def
  unfolding impl.emptiness_check_impl_def
  unfolding impl.state_copy_impl_def
  .

lemmas no_deadlock_certifier_hnr' =
  impl.deadlock_unreachability_checker_hnr[folded no_deadlock_certifier_def,
    OF state_impl_abstract',
    OF _ A assms(2,3) impl.L_dom_M_eqI[OF state_impl_abstract' A assms(2,3)]
       split_k_full_split list_assn_split,
    unfolded deadlock_prod
  ]



schematic_goal unreachability_checker2_alt_def:
  "impl.unreachability_checker2 L_list M_list (split_k num_split) \<equiv> ?x"
  apply (subst impl.unreachability_checker2_def[
      OF state_impl_abstract', OF _ A assms(2,3) split_k_full_split list_assn_split
      ], (simp; fail))
  apply (subst impl.M_table_def[OF state_impl_abstract', of states'_memi, OF _ A assms(2,3)])
   apply assumption
  unfolding check_deadlock_impl_alt_def impl.P_impl_def impl.F_impl_def
  apply (abstract_let states'_memi check_states)
  unfolding states'_memi_def states_mem_compute'
  apply (abstract_let "map states_i [0..<n_ps]" states_i)
  unfolding succs_impl_alt_def
  unfolding k_impl_alt_def k_i_def
  (* The following are just to unfold things that should have been defined in a defs locale *)
  unfolding impl.E_op''_impl_def impl.abstr_repair_impl_def impl.abstra_repair_impl_def
  unfolding
    impl.start_inv_check_impl_def impl.unbounded_dbm_impl_def
    impl.unbounded_dbm'_def
  unfolding impl.init_dbm_impl_def impl.a\<^sub>0_impl_def
  unfolding impl.subsumes_impl_def
  unfolding impl.emptiness_check_impl_def
  unfolding impl.state_copy_impl_def
  by (rule Pure.reflexive)

definition no_deadlock_certifier2 where
  "no_deadlock_certifier2 \<equiv>
  Reachability_Problem_Impl_Precise.unreachability_checker2
    m trans_impl l\<^sub>0i (PR_CONST impl.E_precise_op'_impl)
    states'_memi (\<lambda>(l, M). impl.check_deadlock_impl l M \<bind> (\<lambda>r. Heap_Monad.return (\<not> r)))"

schematic_goal no_deadlock_certifier2_alt_def:
  "no_deadlock_certifier2 L_list M_list (split_k num_split) \<equiv> ?x"
  unfolding no_deadlock_certifier2_def
  apply (subst impl.deadlock_unreachability_checker2_def[
        OF state_impl_abstract', OF _ A assms(2,3) split_k_full_split list_assn_split
        ], (simp; fail))
  apply (subst impl.M_table_def[OF state_impl_abstract', of states'_memi, OF _ A assms(2,3)])
   apply assumption
  unfolding check_deadlock_impl_alt_def impl.P_impl_def
  apply (abstract_let states'_memi check_states)
  unfolding states'_memi_def states_mem_compute'
  apply (abstract_let "map states_i [0..<n_ps]" states_i)
  unfolding succs_impl_alt_def
  unfolding k_impl_alt_def k_i_def
  (* The following are just to unfold things that should have been defined in a defs locale *)
  unfolding impl.E_op''_impl_def impl.abstr_repair_impl_def impl.abstra_repair_impl_def
  unfolding
    impl.start_inv_check_impl_def impl.unbounded_dbm_impl_def
    impl.unbounded_dbm'_def
  unfolding impl.init_dbm_impl_def impl.a\<^sub>0_impl_def
  unfolding impl.subsumes_impl_def
  unfolding impl.emptiness_check_impl_def
  unfolding impl.state_copy_impl_def
  by (rule Pure.reflexive)

lemmas no_deadlock_certifier2_refine' =
  impl.deadlock_unreachability_checker2_hnr[
    folded no_deadlock_certifier2_def,
    OF state_impl_abstract' A assms(3) _ split_k_full_split list_assn_split
  ]

schematic_goal unreachability_checker3_alt_def:
  "impl.certify_unreachable_pure L_list M_list (split_k' num_split M_list) \<equiv> ?x"
  if "fst ` set M_list = set L_list"
  apply (subst impl.certify_unreachable_pure_def[
      OF state_impl_abstract', OF _ A assms(2,3) split_k'_full_split[of M_list, unfolded that]
      ], (simp; fail))
  apply (abstract_let "impl.init_dbm_impl :: int DBMEntry Heap.array Heap" init_dbm)
  unfolding impl.init_dbm_impl_def
  apply (abstract_let "impl.Mi M_list" Mi)
  apply (subst impl.Mi_def[OF state_impl_abstract', of states'_memi, OF _ A assms(2,3)])
   apply assumption
  unfolding check_deadlock_impl_alt_def impl.P_impl_def impl.F_impl_def
  apply (abstract_let states'_memi check_state)
  unfolding states'_memi_def states_mem_compute'
  apply (abstract_let "map states_i [0..<n_ps]" states_i)
  apply (abstract_let "impl.succs_precise'_impl" succsi)
  unfolding succs_impl.refine[OF Simple_Network_Impl_nat_ceiling_start_state_axioms] succs1_refine
  apply (abstract_let invs2 invs)
  unfolding invs2_def
  apply (abstract_let n_ps n_ps)
  apply (abstract_let n_vs n_vs)
  .


schematic_goal check_deadlock_impl_alt_def2:
  "impl.check_deadlock_impl \<equiv> ?impl"
  unfolding impl.check_deadlock_impl_def
  apply (abstract_let trans_impl trans_impl)
  unfolding trans_impl_alt_def
  apply (abstract_let "inv_fun :: nat list \<times> int list \<Rightarrow> _" inv_fun)
  unfolding inv_fun_alt_def
  apply (abstract_let invs2 invs)
  unfolding invs2_def
  apply (abstract_let n_ps n_ps)
  .

definition no_deadlock_certifier3 where
  "no_deadlock_certifier3 \<equiv>
  Reachability_Problem_Impl_Precise.certify_unreachable_pure
    m trans_impl l\<^sub>0i (PR_CONST impl.E_precise_op'_impl)
    states'_memi (\<lambda>(l, M). impl.check_deadlock_impl l M \<bind> (\<lambda>r. Heap_Monad.return (\<not> r)))"

definition
  "check_deadlock_fold = (\<lambda>a. run_heap ((case a of (l, s) \<Rightarrow> array_unfreeze s
  \<bind> (\<lambda>s. Heap_Monad.return (id l, s)))
  \<bind> (\<lambda>a. case a of (l, M) \<Rightarrow> impl.check_deadlock_impl l M
  \<bind> (\<lambda>r. Heap_Monad.return (\<not> r)))))"

schematic_goal no_deadlock_certifier3_alt_def:
  "no_deadlock_certifier3 L_list M_list (split_k' num_split M_list) \<equiv> ?x"
  if "fst ` set M_list = set L_list"
  unfolding no_deadlock_certifier3_def
  apply (subst impl.deadlock_unreachability_checker3_def[
        OF state_impl_abstract', OF _ A assms(2,3) split_k'_full_split[of M_list, unfolded that]
        ], (simp; fail))
  unfolding check_deadlock_fold_def[symmetric]
  apply (abstract_let check_deadlock_fold check_deadlock1)
  unfolding check_deadlock_fold_def
  apply (abstract_let impl.check_deadlock_impl check_deadlock)
  apply (abstract_let "impl.init_dbm_impl :: int DBMEntry Heap.array Heap" init_dbm)
  unfolding impl.init_dbm_impl_def
  apply (abstract_let "impl.Mi M_list" Mi)
  apply (subst impl.Mi_def[OF state_impl_abstract', of states'_memi, OF _ A assms(2,3)])
   apply assumption
  apply (abstract_let "(\<lambda>a :: (nat list \<times> int list) \<times> int DBMEntry iarray. run_heap
      ((case a of (l, s) \<Rightarrow> array_unfreeze s \<bind> (\<lambda>s. Heap_Monad.return (id l, s))) \<bind> impl.P_impl))"
      P)
  apply (abstract_let "impl.P_impl :: _ \<times> int DBMEntry Heap.array \<Rightarrow> _" P_impl)
  apply (abstract_let "(\<lambda>(as :: int DBMEntry iarray) bs.
            (\<exists>i\<le>m. as !! (i + i * m + i) < Le 0) \<or> array_all2 (Suc m * Suc m) (\<le>) as bs)"
    subsumption)
  unfolding check_deadlock_impl_alt_def2
  unfolding impl.P_impl_def impl.F_impl_def
  apply (abstract_let states'_memi check_states)
  unfolding states'_memi_def states_mem_compute'
  apply (abstract_let "map states_i [0..<n_ps]" states_i)
  apply (abstract_let "impl.succs_precise'_impl" succsi)
  unfolding succs_impl.refine[OF Simple_Network_Impl_nat_ceiling_start_state_axioms] succs1_refine
  apply (abstract_let invs2 invs)
  unfolding invs2_def
  apply (abstract_let n_ps n_ps)
  apply (abstract_let n_vs n_vs)
  .

lemma no_deadlock_certifier3_refine':
    "no_deadlock_certifier3 L_list M_list (split_k' num_split M_list)
    \<longrightarrow> (\<forall>u. (\<forall>c\<le>m. u c = 0) \<longrightarrow> \<not> reach.deadlock (l\<^sub>0, u))" if "fst ` set M_list = set L_list"
  by (rule impl.deadlock_unreachability_checker3_hnr[
    folded no_deadlock_certifier3_def, OF state_impl_abstract' A assms(3)
  ]) (simp add: that split_k'_full_split[symmetric])+

end (* Anonymous context *)

theorem no_deadlock_certifier_hnr:
  assumes "list_all states'_memi L_list"
      and "list_all (\<lambda>(l, y). list_all (\<lambda>M. length M = Suc m * Suc m) y) M_list"
      and "fst ` set M_list = set L_list"
  shows "(
  uncurry0 (no_deadlock_certifier L_list M_list (split_k num_split)),
  uncurry0 (SPEC (\<lambda>r. r \<longrightarrow>
    \<not> has_deadlock (Simple_Network_Language.conv A) (L\<^sub>0, map_of s\<^sub>0, \<lambda>_. 0))))
  \<in> unit_assn\<^sup>k \<rightarrow>\<^sub>a bool_assn"
proof -
  define checker where "checker \<equiv> no_deadlock_certifier L_list M_list"
  define P where "P \<equiv> reach.deadlock"
  note *[sep_heap_rules] =
    no_deadlock_certifier_hnr'[
      OF assms(1) _ assms(2),
      to_hnr, unfolded hn_refine_def, rule_format, folded checker_def P_def
      ]
  from assms(3) show ?thesis
    unfolding checker_def[symmetric] deadlock_prod[symmetric] P_def[symmetric]
    by sepref_to_hoare (sep_auto simp: pure_def)
qed

theorem no_deadlock_certifier2_refine:
  assumes "list_all states'_memi L_list"
      and "list_all (\<lambda>(l, y). list_all (\<lambda>M. length M = Suc m * Suc m) y) M_list"
      and "fst ` set M_list = set L_list"
  shows "no_deadlock_certifier2 L_list M_list (split_k num_split) \<longrightarrow>
    \<not> has_deadlock (Simple_Network_Language.conv A) (L\<^sub>0, map_of s\<^sub>0, \<lambda>_. 0)"
  using no_deadlock_certifier2_refine'[OF assms(1) _ assms(2), of num_split] assms(3)
  unfolding deadlock_prod[symmetric] by auto

theorem no_deadlock_certifier3_refine:
  assumes "list_all states'_memi L_list"
      and "list_all (\<lambda>(l, y). list_all (\<lambda>M. length M = Suc m * Suc m) y) M_list"
      and "fst ` set M_list = set L_list"
  shows "no_deadlock_certifier3 L_list M_list (split_k' num_split M_list) \<longrightarrow>
    \<not> has_deadlock (Simple_Network_Language.conv A) (L\<^sub>0, map_of s\<^sub>0, \<lambda>_. 0)"
  using no_deadlock_certifier3_refine' assms unfolding deadlock_prod[symmetric] by auto

definition
  "show_dbm_impl' M \<equiv> do {
  s \<leftarrow> show_dbm_impl m show_clock show M;
  Heap_Monad.return (String.implode s)
}"

definition
  "show_state_impl l \<equiv> do {
    let s = show_state l;
    let s = String.implode s;
    Heap_Monad.return s
  }"

definition
  "trace_table M_table \<equiv> do {
    M_list' \<leftarrow> list_of_map_impl M_table;
    let _ = println STR ''Inverted table'';
    Heap_Monad.fold_map (\<lambda> (l, xs). do {
      s1 \<leftarrow> show_state_impl l;
      let _ = println (s1 + STR '':'');
      Heap_Monad.fold_map (\<lambda>M.  do {
        s2 \<leftarrow> show_dbm_impl_all m show_clock show M;
        let _ = println (STR ''  '' + String.implode s2);
        Heap_Monad.return ()
      }) xs;
      Heap_Monad.return ()
    }) M_list';
    Heap_Monad.return ()
  }" for M_table

definition
  "check_prop_fail L_list M_list \<equiv> let
    P_impl = impl.P_impl;
    copy = amtx_copy;
    show_dbm = show_dbm_impl';
    show_state = show_state_impl
   in do {
    M_table \<leftarrow> M_table M_list;

    trace_table M_table;

    r \<leftarrow> check_prop_fail_impl P_impl copy show_dbm show_state L_list M_table;
    case r of None \<Rightarrow> Heap_Monad.return () | Some (l, M) \<Rightarrow> do {
      let b = states'_memi l;
      let _ = println (if b then STR ''State passed'' else STR ''State failed'');
      b \<leftarrow> check_diag_impl m M;
      let _ = println (if b then STR ''DBM passed diag'' else STR ''DBM failed diag'');
      b \<leftarrow> check_diag_nonpos m M;
      let _ = println (if b then STR ''DBM passed diag nonpos'' else STR ''DBM failed diag nonpos'');
       b \<leftarrow> check_nonneg m M;
      let _ = println (if b then STR ''DBM passed nonneg'' else STR ''DBM failed nonneg'');
      s \<leftarrow> show_dbm_impl_all m show_clock show M;
      let _ = println (STR ''DBM: '' + String.implode s);
      Heap_Monad.return ()
    }
   }"

definition 
  "check_invariant_fail \<equiv> \<lambda>L_list M_list. let
    copy = amtx_copy;
    succs = impl.succs_precise'_impl;
    Lei = dbm_subset_impl m;
    show_state = show_state_impl;
    show_dbm = show_dbm_impl_all m show_clock show
  in do {
    M_table \<leftarrow> M_table M_list;
    r \<leftarrow> check_invariant_fail_impl copy Lei succs L_list M_table;
    case r of None \<Rightarrow> Heap_Monad.return ()
    | Some (Inl (Inl (l, l', xs))) \<Rightarrow> do {
        let _ = println (STR ''The successor is not contained in L:'');
        s \<leftarrow> show_state l;
        let _ = println (STR ''  '' + s);
        s \<leftarrow> show_state l';
        let _ = println (STR ''  '' + s);
        Heap_Monad.fold_map (\<lambda>M. do {
          s \<leftarrow> show_dbm M;
          let _ = println (STR '' '' + String.implode s);
          Heap_Monad.return ()
        }) xs;
        Heap_Monad.return ()
      }
    | Some (Inl (Inr (l, l', xs))) \<Rightarrow> do {
        let _ = println (STR ''The successor is not empty:'');
        s \<leftarrow> show_state l;
        let _ = println (STR ''  '' + s);
        s \<leftarrow> show_state l';
        let _ = println (STR ''  '' + s);
        Heap_Monad.fold_map (\<lambda>M. do {
          s \<leftarrow> show_dbm M;
          let _ = println (STR '' '' + String.implode s);
          Heap_Monad.return ()
        }) xs;
        Heap_Monad.return ()
      }
    | Some (Inr (l, M)) \<Rightarrow> do {
        s1 \<leftarrow> show_state l;
        s2 \<leftarrow> show_dbm M;
        let _ = println (STR ''A pair failed: '' + s1);
        let _ = println (STR ''  '' + String.implode s2);
        Heap_Monad.return ()
      }
  }
"

schematic_goal check_prop_fail_alt_def:
  "check_prop_fail \<equiv> ?t"
  unfolding check_prop_fail_def
  unfolding M_table_def trace_table_def
  unfolding impl.P_impl_def
  unfolding show_dbm_impl'_def
  unfolding show_state_impl_def
  apply (abstract_let states'_memi check_states)
  unfolding states'_memi_def states_mem_compute'
  apply (abstract_let "map states_i [0..<n_ps]" states_i)
  by (rule Pure.reflexive)

schematic_goal check_invariant_fail_alt_def:
  "check_invariant_fail \<equiv> ?t"
  unfolding check_invariant_fail_def
  unfolding M_table_def
  unfolding succs_impl_alt_def
  (* The following are just to unfold things that should have been defined in a defs locale *)
  unfolding impl.E_op''_impl_def impl.abstr_repair_impl_def impl.abstra_repair_impl_def
  unfolding impl.subsumes_impl_def
  unfolding impl.emptiness_check_impl_def
  unfolding impl.state_copy_impl_def
  unfolding show_dbm_impl'_def show_state_impl_def
  by (rule Pure.reflexive)

end (* Simple_Network_Impl_nat_ceiling_start_state *)

concrete_definition unreachability_checker uses
  Simple_Network_Impl_nat_ceiling_start_state.unreachability_checker_alt_def

concrete_definition no_deadlock_certifier uses
  Simple_Network_Impl_nat_ceiling_start_state.no_deadlock_certifier_alt_def

concrete_definition unreachability_checker2 uses
  Simple_Network_Impl_nat_ceiling_start_state.unreachability_checker2_alt_def

concrete_definition no_deadlock_certifier2 uses
  Simple_Network_Impl_nat_ceiling_start_state.no_deadlock_certifier2_alt_def

concrete_definition unreachability_checker3 uses
  Simple_Network_Impl_nat_ceiling_start_state.unreachability_checker3_alt_def

concrete_definition no_deadlock_certifier3 uses
  Simple_Network_Impl_nat_ceiling_start_state.no_deadlock_certifier3_alt_def

concrete_definition check_prop_fail uses
  Simple_Network_Impl_nat_ceiling_start_state.check_prop_fail_alt_def

concrete_definition check_invariant_fail uses
  Simple_Network_Impl_nat_ceiling_start_state.check_invariant_fail_alt_def

lemma states'_memi_alt_def:
  "Simple_Network_Impl_nat_defs.states'_memi broadcast bounds' automata = (
     \<lambda>(L, s).
    let
      n_ps = length automata;
      n_vs = Simple_Network_Impl_Defs.n_vs bounds';
      states_i = map (Simple_Network_Impl_nat_defs.states_i automata) [0..<n_ps]
    in
      length L = n_ps \<and> (\<forall>i<n_ps. L ! i \<in> states_i ! i) \<and>
      length s = n_vs \<and> Simple_Network_Impl_nat_defs.check_boundedi bounds' s
    )
    "
  unfolding Simple_Network_Impl_nat_defs.states'_memi_def
  unfolding Simple_Network_Impl_nat_defs.states_mem_compute'
  unfolding Prod_TA_Defs.n_ps_def list_all_iff
  by (intro ext) simp

definition
  "certificate_checker_pre
    L_list M_list broadcast bounds' automata m num_states num_actions k L\<^sub>0 s\<^sub>0 formula
  \<equiv>
  let
    _ = start_timer ();
    check1 = Simple_Network_Impl_nat_ceiling_start_state
      broadcast bounds' automata m num_states num_actions k L\<^sub>0 s\<^sub>0 formula;
    _ = save_time STR ''Time to check ceiling'';
    n_ps = length automata;
    n_vs = Simple_Network_Impl_Defs.n_vs bounds';
    states_i = map (Simple_Network_Impl_nat_defs.states_i automata) [0..<n_ps];
    _ = start_timer ();
    check2 = list_all (\<lambda>(L, s). length L = n_ps \<and> (\<forall>i<n_ps. L ! i \<in> states_i ! i) \<and>
      length s = n_vs \<and> Simple_Network_Impl_nat_defs.check_boundedi bounds' s
    ) L_list;
    _ = save_time STR ''Time to check states'';
    _ = start_timer ();
    n_sq = Suc m * Suc m;
    check3 = list_all (\<lambda>(l, xs). list_all (\<lambda>M. length M = n_sq) xs) M_list;
    _ = save_time STR ''Time to check DBMs'';
    check4 = (case formula of formula.EX _ \<Rightarrow> True | _ \<Rightarrow> False)
  in check1 \<and> check2 \<and> check3 \<and> check4"

definition
  "certificate_checker num_split dc
    M_list broadcast bounds' automata m num_states num_actions k L\<^sub>0 s\<^sub>0 formula
    (* inv_renum_states inv_renum_vars inv_renum_clocks *)
  \<equiv>
  let
    L_list = map fst M_list;
    check = certificate_checker_pre
      L_list M_list broadcast bounds' automata m num_states num_actions k L\<^sub>0 s\<^sub>0 formula
    (*;
    show_c = show_clock inv_renum_clocks;
    show_st = show_state inv_renum_states inv_renum_vars *)
  in if check then
  do {
    r \<leftarrow>
      if dc then
        no_deadlock_certifier
          broadcast bounds' automata m num_states num_actions L\<^sub>0 s\<^sub>0 L_list M_list num_split
      else
        unreachability_checker
          broadcast bounds' automata m num_states num_actions L\<^sub>0 s\<^sub>0 formula L_list M_list num_split;
    Heap_Monad.return (Some r)
  } else Heap_Monad.return None"

definition
  "certificate_checker2 num_split dc
    M_list broadcast bounds' automata m num_states num_actions k L\<^sub>0 s\<^sub>0 formula
  \<equiv>
  let
    L_list = map fst M_list;
    check = certificate_checker_pre
      L_list M_list broadcast bounds' automata m num_states num_actions k L\<^sub>0 s\<^sub>0 formula
  in if check then
    if dc then
        no_deadlock_certifier2
          broadcast bounds' automata m num_states num_actions L\<^sub>0 s\<^sub>0 L_list M_list num_split
      else
        unreachability_checker2
          broadcast bounds' automata m num_states num_actions L\<^sub>0 s\<^sub>0 formula L_list M_list num_split
  else False"

definition
  "certificate_checker3 num_split dc
    M_list broadcast bounds' automata m num_states num_actions k L\<^sub>0 s\<^sub>0 formula
  \<equiv>
  let
    L_list = map fst M_list;
    check = certificate_checker_pre
      L_list M_list broadcast bounds' automata m num_states num_actions k L\<^sub>0 s\<^sub>0 formula
  in if check then
    if dc then
        no_deadlock_certifier3
          broadcast bounds' automata m num_states num_actions L\<^sub>0 s\<^sub>0 L_list M_list num_split
      else
        unreachability_checker3
          broadcast bounds' automata m num_states num_actions L\<^sub>0 s\<^sub>0 formula L_list M_list num_split
  else False"

definition
  "certificate_checker_dbg num_split
    (show_clock :: (nat \<Rightarrow> string)) (show_state :: (nat list \<times> int list \<Rightarrow> char list))
    M_list broadcast bounds' automata m num_states num_actions k L\<^sub>0 s\<^sub>0 formula
  \<equiv>
  let
    _ = start_timer ();
    check1 = Simple_Network_Impl_nat_ceiling_start_state
      broadcast bounds' automata m num_states num_actions k L\<^sub>0 s\<^sub>0 formula;
    _ = save_time STR ''Time to check ceiling'';
    L_list = map fst M_list;
    n_ps = length automata;
    n_vs = Simple_Network_Impl_Defs.n_vs bounds';
    states_i = map (Simple_Network_Impl_nat_defs.states_i automata) [0..<n_ps];
    _ = start_timer ();
    check2 = list_all (\<lambda>(L, s). length L = n_ps \<and> (\<forall>i<n_ps. L ! i \<in> states_i ! i) \<and>
      length s = n_vs \<and> Simple_Network_Impl_nat_defs.check_boundedi bounds' s
    ) L_list;
    _ = save_time STR ''Time to check states'';
    check3 = (case formula of formula.EX _ \<Rightarrow> True | _ \<Rightarrow> False)
  in if check1 \<and> check2 \<and> check3 then
  do {
    check_prop_fail broadcast bounds' automata m show_clock show_state L_list M_list;
    check_invariant_fail broadcast bounds' automata m
      num_states num_actions show_clock show_state L_list M_list;
    r \<leftarrow> unreachability_checker
      broadcast bounds' automata m num_states num_actions L\<^sub>0 s\<^sub>0 formula L_list M_list num_split;
    Heap_Monad.return (Some r)
  } else Heap_Monad.return None" for show_clock show_state

theorem certificate_check:
  "<emp> certificate_checker num_split False
    M_list broadcast bounds automata m num_states num_actions k L\<^sub>0 s\<^sub>0 formula
    (* inv_renum_states inv_renum_vars inv_renum_clocks *)
   <\<lambda> Some r \<Rightarrow> \<up>(r \<longrightarrow> \<not> N broadcast automata bounds,(L\<^sub>0, map_of s\<^sub>0, \<lambda>_ . 0) \<Turnstile> formula)
    | None \<Rightarrow> true>\<^sub>t"
proof -
  define A where "A \<equiv> N broadcast automata bounds"
  define check where "check \<equiv> A,(L\<^sub>0, map_of s\<^sub>0, \<lambda>_ . 0) \<Turnstile> formula"
  { fix \<phi> assume A: "formula = formula.EX \<phi>"
    note
      Simple_Network_Impl_nat_ceiling_start_state.unreachability_checker_hnr[
        of broadcast bounds automata m num_states num_actions k L\<^sub>0 s\<^sub>0 formula
           "Simple_Network_Impl_nat_defs.states'_memi broadcast bounds automata"
           "map fst M_list" M_list,
        folded A_def check_def,
        to_hnr, unfolded hn_refine_def, rule_format,
        OF _ _ _ _ _ A, unfolded A]
  } note *[sep_heap_rules] = this[simplified, unfolded hd_of_formulai.simps[abs_def]]
  show ?thesis
    unfolding A_def[symmetric] check_def[symmetric]
    unfolding certificate_checker_def certificate_checker_pre_def
    unfolding Let_def
    unfolding states'_memi_alt_def[unfolded Let_def, symmetric, of automata bounds broadcast]
    by (sep_auto simp: unreachability_checker.refine[symmetric] pure_def split: formula.split_asm)
qed

theorem certificate_deadlock_check:
  "<emp> certificate_checker num_split True
    M_list broadcast bounds automata m num_states num_actions k L\<^sub>0 s\<^sub>0 formula
    (* inv_renum_states inv_renum_vars inv_renum_clocks *)
   <\<lambda> Some r \<Rightarrow> \<up>(r \<longrightarrow> \<not> has_deadlock (N broadcast automata bounds) (L\<^sub>0, map_of s\<^sub>0, \<lambda>_ . 0))
    | None \<Rightarrow> true>\<^sub>t"
proof -
  define A where "A \<equiv> N broadcast automata bounds"
  define check where "check \<equiv> \<not> has_deadlock A (L\<^sub>0, map_of s\<^sub>0, \<lambda>_ . 0)"
  note *[sep_heap_rules] = Simple_Network_Impl_nat_ceiling_start_state.no_deadlock_certifier_hnr[
      of broadcast bounds automata m num_states num_actions k L\<^sub>0 s\<^sub>0 formula
         "map fst M_list" M_list,
      folded A_def check_def,
      to_hnr, unfolded hn_refine_def, rule_format, unfolded hd_of_formulai.simps[abs_def]
  ]
  show ?thesis
    unfolding A_def[symmetric] check_def[symmetric]
    unfolding certificate_checker_def certificate_checker_pre_def
    unfolding Let_def
    unfolding states'_memi_alt_def[unfolded Let_def, symmetric, of automata bounds broadcast]
    by (sep_auto simp: no_deadlock_certifier.refine[symmetric] pure_def split: formula.split_asm)
qed

theorem certificate_check2:
  "certificate_checker2 num_split False
    M_list broadcast bounds automata m num_states num_actions k L\<^sub>0 s\<^sub>0 formula
   \<longrightarrow> \<not> N broadcast automata bounds,(L\<^sub>0, map_of s\<^sub>0, \<lambda>_ . 0) \<Turnstile> formula"
  using Simple_Network_Impl_nat_ceiling_start_state.unreachability_checker2_refine[
      of broadcast bounds automata m num_states num_actions k L\<^sub>0 s\<^sub>0 formula
         "Simple_Network_Impl_nat_defs.states'_memi broadcast bounds automata"
         "map fst M_list" M_list
         ]
  unfolding certificate_checker2_def certificate_checker_pre_def
  unfolding Let_def
  unfolding states'_memi_alt_def[unfolded Let_def, symmetric, of automata bounds broadcast]
  by (clarsimp split: formula.split_asm simp: unreachability_checker2.refine[symmetric])

theorem certificate_deadlock_check2:
  "certificate_checker2 num_split True
    M_list broadcast bounds automata m num_states num_actions k L\<^sub>0 s\<^sub>0 formula
   \<longrightarrow> \<not> has_deadlock (N broadcast automata bounds) (L\<^sub>0, map_of s\<^sub>0, \<lambda>_ . 0)"
  using Simple_Network_Impl_nat_ceiling_start_state.no_deadlock_certifier2_refine[
      of broadcast bounds automata m num_states num_actions k L\<^sub>0 s\<^sub>0 formula
         "map fst M_list" M_list num_split
         ]
  unfolding certificate_checker2_def certificate_checker_pre_def Let_def
  unfolding states'_memi_alt_def[unfolded Let_def, symmetric, of automata bounds broadcast]
  by (clarsimp simp: no_deadlock_certifier2.refine[symmetric])

theorem certificate_check3:
  "certificate_checker3 num_split False
    M_list broadcast bounds automata m num_states num_actions k L\<^sub>0 s\<^sub>0 formula
   \<longrightarrow> \<not> N broadcast automata bounds,(L\<^sub>0, map_of s\<^sub>0, \<lambda>_ . 0) \<Turnstile> formula"
  using Simple_Network_Impl_nat_ceiling_start_state.unreachability_checker3_refine[
      of broadcast bounds automata m num_states num_actions k L\<^sub>0 s\<^sub>0 formula
         "Simple_Network_Impl_nat_defs.states'_memi broadcast bounds automata"
         "map fst M_list" M_list
         ]
  unfolding certificate_checker3_def certificate_checker_pre_def
  unfolding Let_def
  unfolding states'_memi_alt_def[unfolded Let_def, symmetric, of automata bounds broadcast]
  by (clarsimp split: formula.split_asm simp: unreachability_checker3.refine[symmetric])

theorem certificate_deadlock_check3:
  "certificate_checker3 num_split True
    M_list broadcast bounds automata m num_states num_actions k L\<^sub>0 s\<^sub>0 formula
   \<longrightarrow> \<not> has_deadlock (N broadcast automata bounds) (L\<^sub>0, map_of s\<^sub>0, \<lambda>_ . 0)"
  using Simple_Network_Impl_nat_ceiling_start_state.no_deadlock_certifier3_refine[
      of broadcast bounds automata m num_states num_actions k L\<^sub>0 s\<^sub>0 formula
         "map fst M_list" M_list
         ]
  unfolding certificate_checker3_def certificate_checker_pre_def Let_def
  unfolding states'_memi_alt_def[unfolded Let_def, symmetric, of automata bounds broadcast]
  by (clarsimp simp: no_deadlock_certifier3.refine[symmetric])

definition rename_check where
  "rename_check num_split dc broadcast bounds' automata k L\<^sub>0 s\<^sub>0 formula
    m num_states num_actions renum_acts renum_vars renum_clocks renum_states
    (* inv_renum_states inv_renum_vars inv_renum_clocks *)
    state_space
\<equiv>
do {
  let r = do_rename_mc (
      \<lambda>(show_clock :: (nat \<Rightarrow> string)) (show_state :: (nat list \<times> int list \<Rightarrow> char list)).
      certificate_checker num_split dc state_space)
    dc broadcast bounds' automata k STR ''_urge'' L\<^sub>0 s\<^sub>0 formula
    m num_states num_actions renum_acts renum_vars renum_clocks renum_states
    (* inv_renum_states inv_renum_vars inv_renum_clocks; *)
    (\<lambda>_ _. '' '') (\<lambda>_. '' '') (\<lambda>_. '' '');
  case r of Some r \<Rightarrow> do {
    r \<leftarrow> r;
    case r of
      None \<Rightarrow> Heap_Monad.return Preconds_Unsat
    | Some False \<Rightarrow> Heap_Monad.return Unsat
    | Some True \<Rightarrow> Heap_Monad.return Sat
  }
  | None \<Rightarrow> Heap_Monad.return Renaming_Failed
}
"

definition rename_check2 where
  "rename_check2 num_split dc broadcast bounds' automata k L\<^sub>0 s\<^sub>0 formula
    m num_states num_actions renum_acts renum_vars renum_clocks renum_states
    state_space
\<equiv>
  let r = do_rename_mc (
      \<lambda>(show_clock :: (nat \<Rightarrow> string)) (show_state :: (nat list \<times> int list \<Rightarrow> char list)).
      certificate_checker2 num_split dc state_space)
    dc broadcast bounds' automata k STR ''_urge'' L\<^sub>0 s\<^sub>0 formula
    m num_states num_actions renum_acts renum_vars renum_clocks renum_states
    (\<lambda>_ _. '' '') (\<lambda>_. '' '') (\<lambda>_. '' '')
  in case r of
    Some False \<Rightarrow> Unsat
  | Some True \<Rightarrow> Sat
  | None \<Rightarrow> Renaming_Failed
"

definition rename_check3 where
  "rename_check3 num_split dc broadcast bounds' automata k L\<^sub>0 s\<^sub>0 formula
    m num_states num_actions renum_acts renum_vars renum_clocks renum_states
    state_space
\<equiv>
  let r = do_rename_mc (
      \<lambda>(show_clock :: (nat \<Rightarrow> string)) (show_state :: (nat list \<times> int list \<Rightarrow> string)).
      certificate_checker3 num_split dc state_space)
    dc broadcast bounds' automata k STR ''_urge'' L\<^sub>0 s\<^sub>0 formula
    m num_states num_actions renum_acts renum_vars renum_clocks renum_states
    (\<lambda>_ _. '' '') (\<lambda>_. '' '') (\<lambda>_. '' '')
  in case r of
    Some False \<Rightarrow> Unsat
  | Some True \<Rightarrow> Sat
  | None \<Rightarrow> Renaming_Failed
"

definition rename_check_dbg where
  "rename_check_dbg num_split dc broadcast bounds' automata k L\<^sub>0 s\<^sub>0 formula
    m num_states num_actions renum_acts renum_vars renum_clocks renum_states
    inv_renum_states inv_renum_vars inv_renum_clocks
    state_space
\<equiv>
do {
  let r = do_rename_mc (
      \<lambda>(show_clock :: (nat \<Rightarrow> string)) (show_state :: (nat list \<times> int list \<Rightarrow> string)).
      certificate_checker_dbg num_split show_clock show_state state_space)
    dc broadcast bounds' automata k STR ''_urge'' L\<^sub>0 s\<^sub>0 formula
    m num_states num_actions renum_acts renum_vars renum_clocks renum_states
    inv_renum_states inv_renum_vars inv_renum_clocks;
  case r of Some r \<Rightarrow> do {
    r \<leftarrow> r;
    case r of
      None \<Rightarrow> Heap_Monad.return Preconds_Unsat
    | Some False \<Rightarrow> Heap_Monad.return Unsat
    | Some True \<Rightarrow> Heap_Monad.return Sat
  }
  | None \<Rightarrow> Heap_Monad.return Renaming_Failed
}
"

theorem certificate_check_rename:
  "<emp> rename_check num_split False broadcast bounds automata k L\<^sub>0 s\<^sub>0 formula
    m num_states num_actions renum_acts renum_vars renum_clocks renum_states
    (* inv_renum_states inv_renum_vars inv_renum_clocks *)
    state_space
    <\<lambda> Sat \<Rightarrow> \<up>(
        (\<not> N broadcast automata bounds,(L\<^sub>0, map_of s\<^sub>0, \<lambda>_ . 0) \<Turnstile> formula))
     | Renaming_Failed \<Rightarrow> \<up>(\<not> Simple_Network_Rename_Formula
        broadcast bounds
        renum_acts renum_vars renum_clocks renum_states STR ''_urge''
        automata formula s\<^sub>0 L\<^sub>0)
     | Unsat \<Rightarrow> true
     | Preconds_Unsat \<Rightarrow> true
    >\<^sub>t" (is ?A)
and certificate_check_rename2:
  "case rename_check2 num_split False broadcast bounds automata k L\<^sub>0 s\<^sub>0 formula
      m num_states num_actions renum_acts renum_vars renum_clocks renum_states
      state_space
    of 
      Sat \<Rightarrow> \<not> N broadcast automata bounds,(L\<^sub>0, map_of s\<^sub>0, \<lambda>_ . 0) \<Turnstile> formula
    | Renaming_Failed \<Rightarrow> \<not> Simple_Network_Rename_Formula
          broadcast bounds
        renum_acts renum_vars renum_clocks renum_states STR ''_urge''
        automata formula s\<^sub>0 L\<^sub>0
    | Unsat \<Rightarrow> True
    | Preconds_Unsat \<Rightarrow> True" (is ?B)
and certificate_check_rename3:
  "case rename_check3 num_split False broadcast bounds automata k L\<^sub>0 s\<^sub>0 formula
      m num_states num_actions renum_acts renum_vars renum_clocks renum_states
      state_space
    of 
      Sat \<Rightarrow> \<not> N broadcast automata bounds,(L\<^sub>0, map_of s\<^sub>0, \<lambda>_ . 0) \<Turnstile> formula
    | Renaming_Failed \<Rightarrow> \<not> Simple_Network_Rename_Formula
        broadcast bounds
        renum_acts renum_vars renum_clocks renum_states STR ''_urge''
        automata formula s\<^sub>0 L\<^sub>0
    | Unsat \<Rightarrow> True
    | Preconds_Unsat \<Rightarrow> True" (is ?C)
proof -
  let ?urge = "STR ''_urge''"
  let ?automata = "map (conv_urge ?urge) automata"
  have *: "
    Simple_Network_Rename_Formula_String
        broadcast bounds
        renum_acts renum_vars renum_clocks renum_states
        automata ?urge formula s\<^sub>0 L\<^sub>0
  = Simple_Network_Rename_Formula
        broadcast bounds
        renum_acts renum_vars renum_clocks renum_states
        ?urge automata formula s\<^sub>0 L\<^sub>0
  "
    unfolding
      Simple_Network_Rename_Formula_String_def Simple_Network_Rename_Formula_def
      Simple_Network_Rename_def Simple_Network_Rename_Formula_axioms_def
    using infinite_literal by auto
  define A where "A \<equiv> N broadcast automata bounds"
  define check where "check \<equiv> A,(L\<^sub>0, map_of s\<^sub>0, \<lambda>_ . 0) \<Turnstile> formula"
  define A' where "A' \<equiv> N
    (map renum_acts broadcast)
    (map_index (renum_automaton renum_acts renum_vars renum_clocks renum_states) ?automata)
    (map (\<lambda>(a,p). (renum_vars a, p)) bounds)"
  define check' where "check' \<equiv>
    A',(map_index renum_states L\<^sub>0, map_of (map (\<lambda>(x, v). (renum_vars x, v)) s\<^sub>0), \<lambda>_ . 0) \<Turnstile>
    map_formula renum_states renum_vars id formula"
  define renaming_valid where "renaming_valid \<equiv>
    Simple_Network_Rename_Formula
      broadcast bounds
      renum_acts renum_vars renum_clocks renum_states STR ''_urge'' automata formula s\<^sub>0 L\<^sub>0
  "
  have [simp]: "check \<longleftrightarrow> check'" 
    if renaming_valid
    using that unfolding check_def check'_def A_def A'_def renaming_valid_def
    by (rule Simple_Network_Rename_Formula.models_iff'[symmetric])
  note [sep_heap_rules] =
    certificate_check[
    of num_split state_space
    "map renum_acts broadcast" "map (\<lambda>(a,p). (renum_vars a, p)) bounds"
    "map_index (renum_automaton renum_acts renum_vars renum_clocks renum_states) ?automata"
    m num_states num_actions k "map_index renum_states L\<^sub>0" "map (\<lambda>(x, v). (renum_vars x, v)) s\<^sub>0"
    "map_formula renum_states renum_vars id formula",
    folded A'_def renaming_valid_def, folded check'_def, simplified
    ]
  show ?A ?B ?C
    using certificate_check2[
      of num_split state_space
      "map renum_acts broadcast" "map (\<lambda>(a,p). (renum_vars a, p)) bounds"
      "map_index (renum_automaton renum_acts renum_vars renum_clocks renum_states) ?automata"
      m num_states num_actions k "map_index renum_states L\<^sub>0" "map (\<lambda>(x, v). (renum_vars x, v)) s\<^sub>0"
      "map_formula renum_states renum_vars id formula",
      folded A'_def renaming_valid_def, folded check'_def
    ]
    using certificate_check3[
      of num_split state_space
      "map renum_acts broadcast" "map (\<lambda>(a,p). (renum_vars a, p)) bounds"
      "map_index (renum_automaton renum_acts renum_vars renum_clocks renum_states) ?automata"
      m num_states num_actions k "map_index renum_states L\<^sub>0" "map (\<lambda>(x, v). (renum_vars x, v)) s\<^sub>0"
      "map_formula renum_states renum_vars id formula",
      folded A'_def renaming_valid_def, folded check'_def
    ]
    unfolding
      rename_check_def rename_check2_def rename_check3_def
      do_rename_mc_def rename_network_def
    unfolding if_False
    unfolding Simple_Network_Rename_Formula_String_Defs.check_renaming[symmetric] * Let_def
    unfolding A_def[symmetric] check_def[symmetric] renaming_valid_def[symmetric]
    by (sep_auto simp: split: bool.splits)+
qed

theorem certificate_deadlock_check_rename:
  "<emp> rename_check num_split True broadcast bounds automata k L\<^sub>0 s\<^sub>0 formula
    m num_states num_actions renum_acts renum_vars renum_clocks renum_states
    (* inv_renum_states inv_renum_vars inv_renum_clocks *)
    state_space
    <\<lambda> Sat \<Rightarrow> \<up>(\<not> has_deadlock (N broadcast automata bounds) (L\<^sub>0, map_of s\<^sub>0, \<lambda>_ . 0))
     | Renaming_Failed \<Rightarrow> \<up>(\<not> Simple_Network_Rename_Formula
        broadcast bounds renum_acts renum_vars renum_clocks renum_states STR ''_urge'' automata
        (formula.EX (sexp.not sexp.true)) s\<^sub>0 L\<^sub>0)
     | Unsat \<Rightarrow> true
     | Preconds_Unsat \<Rightarrow> true
    >\<^sub>t" (is ?A)
and certificate_deadlock_check_rename2:
  "case rename_check2 num_split True broadcast bounds automata k L\<^sub>0 s\<^sub>0 formula
      m num_states num_actions renum_acts renum_vars renum_clocks renum_states
      state_space
    of 
      Sat \<Rightarrow> \<not> has_deadlock (N broadcast automata bounds) (L\<^sub>0, map_of s\<^sub>0, \<lambda>_ . 0)
    | Renaming_Failed \<Rightarrow> \<not> Simple_Network_Rename_Formula
        broadcast bounds renum_acts renum_vars renum_clocks renum_states STR ''_urge'' automata
        (formula.EX (sexp.not sexp.true)) s\<^sub>0 L\<^sub>0
    | Unsat \<Rightarrow> True
    | Preconds_Unsat \<Rightarrow> True" (is ?B)
and certificate_deadlock_check_rename3:
  "case rename_check3 num_split True broadcast bounds automata k L\<^sub>0 s\<^sub>0 formula
      m num_states num_actions renum_acts renum_vars renum_clocks renum_states
      state_space
    of 
      Sat \<Rightarrow> \<not> has_deadlock (N broadcast automata bounds) (L\<^sub>0, map_of s\<^sub>0, \<lambda>_ . 0)
    | Renaming_Failed \<Rightarrow> \<not> Simple_Network_Rename_Formula
        broadcast bounds renum_acts renum_vars renum_clocks renum_states STR ''_urge'' automata
        (formula.EX (sexp.not sexp.true)) s\<^sub>0 L\<^sub>0
    | Unsat \<Rightarrow> True
    | Preconds_Unsat \<Rightarrow> True" (is ?C)
proof -
  let ?formula = "formula.EX (sexp.not sexp.true)"
  let ?urge = "STR ''_urge''"
  let ?automata = "map (conv_urge ?urge) automata"
  have *: "
    Simple_Network_Rename_Formula_String
        broadcast bounds renum_acts renum_vars renum_clocks renum_states automata ?urge ?formula s\<^sub>0 L\<^sub>0
  = Simple_Network_Rename_Formula
        broadcast bounds renum_acts renum_vars renum_clocks renum_states ?urge automata ?formula s\<^sub>0 L\<^sub>0
  "
    unfolding
      Simple_Network_Rename_Formula_String_def Simple_Network_Rename_Formula_def
      Simple_Network_Rename_def Simple_Network_Rename_Formula_axioms_def
    using infinite_literal by auto
  define A where "A \<equiv> N broadcast automata bounds"
  define check where "check \<equiv> has_deadlock A (L\<^sub>0, map_of s\<^sub>0, \<lambda>_ . 0)"
  define A' where "A' \<equiv> N
    (map renum_acts broadcast)
    (map_index (renum_automaton renum_acts renum_vars renum_clocks renum_states) ?automata)
    (map (\<lambda>(a,p). (renum_vars a, p)) bounds)"
  define check' where "check' \<equiv>
    has_deadlock A' (map_index renum_states L\<^sub>0, map_of (map (\<lambda>(x, v). (renum_vars x, v)) s\<^sub>0), \<lambda>_ . 0)"
  define renaming_valid where "renaming_valid \<equiv>
    Simple_Network_Rename_Formula
      broadcast bounds renum_acts renum_vars renum_clocks renum_states ?urge automata ?formula s\<^sub>0 L\<^sub>0
  "
  have **[simp]: "check \<longleftrightarrow> check'" 
    if renaming_valid
    using that unfolding check_def check'_def A_def A'_def renaming_valid_def
    by (rule Simple_Network_Rename_Formula.has_deadlock_iff'[symmetric])
  note [sep_heap_rules] =
    certificate_deadlock_check[
    of num_split state_space
    "map renum_acts broadcast" "map (\<lambda>(a,p). (renum_vars a, p)) bounds"
    "map_index (renum_automaton renum_acts renum_vars renum_clocks renum_states) ?automata"
    m num_states num_actions k "map_index renum_states L\<^sub>0" "map (\<lambda>(x, v). (renum_vars x, v)) s\<^sub>0"
    "map_formula renum_states renum_vars id ?formula",
    folded A'_def renaming_valid_def, folded check'_def, simplified
    ]
  show ?A ?B ?C
    using certificate_deadlock_check2[
      of num_split state_space
      "map renum_acts broadcast" "map (\<lambda>(a, p). (renum_vars a, p)) bounds"
      "map_index (renum_automaton renum_acts renum_vars renum_clocks renum_states) ?automata"
      m num_states num_actions k "map_index renum_states L\<^sub>0" "map (\<lambda>(x, v). (renum_vars x, v)) s\<^sub>0"
      "map_formula renum_states renum_vars id ?formula",
      folded A'_def renaming_valid_def, folded check'_def, simplified
    ]
    using certificate_deadlock_check3[
      of num_split state_space
      "map renum_acts broadcast" "map (\<lambda>(a, p). (renum_vars a, p)) bounds"
      "map_index (renum_automaton renum_acts renum_vars renum_clocks renum_states) ?automata"
      m num_states num_actions k "map_index renum_states L\<^sub>0" "map (\<lambda>(x, v). (renum_vars x, v)) s\<^sub>0"
      "map_formula renum_states renum_vars id ?formula",
      folded A'_def renaming_valid_def, folded check'_def, simplified
    ]
    unfolding
      rename_check_def rename_check2_def rename_check3_def do_rename_mc_def rename_network_def
    unfolding if_True
    unfolding Simple_Network_Rename_Formula_String_Defs.check_renaming[symmetric] * Let_def
    unfolding
      A_def[symmetric] check_def[symmetric] renaming_valid_def[symmetric]
    by (sep_auto split: bool.splits)+
qed

lemmas [code] = Simple_Network_Impl_nat_defs.states_i_def

export_code rename_check rename_check2 rename_check3 in SML module_name Test

export_code rename_check_dbg in SML module_name Test

end