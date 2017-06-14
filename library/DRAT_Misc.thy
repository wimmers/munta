(* Author: Peter Lammich *)
theory DRAT_Misc
imports IICF
begin

  (* TODO: Move *)
  lemma map_nth_upt_drop_take_conv: "N \<le> length l \<Longrightarrow> map (nth l) [M..<N] = drop M (take N l)"
    by (induction N) (auto simp: take_Suc_conv_app_nth)


  (* TODO: Move *)
  lemma insert_minus_eq: "x\<noteq>y \<Longrightarrow> insert x A - {y} = insert x (A - {y})" by auto


  (* TODO: Move. Shouldn't this be detected by simproc? *)
  lemma ex_b_b_and_simp[simp]: "(\<exists>b. b \<and> Q b) \<longleftrightarrow> Q True" by auto
  lemma ex_b_not_b_and_simp[simp]: "(\<exists>b. \<not>b \<and> Q b) \<longleftrightarrow> Q False" by auto


  (* TODO: Move *)
  lemma map_sum_Inr_conv: "map_sum fl fr s = Inr y \<longleftrightarrow> (\<exists>x. s=Inr x \<and> y = fr x)"
    by (cases s) auto
  lemma map_sum_Inl_conv: "map_sum fl fr s = Inl y \<longleftrightarrow> (\<exists>x. s=Inl x \<and> y = fl x)"
    by (cases s) auto

  (* TODO: Move and replace. Too specific type in Relators.thy! *)
  lemma sum_relI:
    "(l,l')\<in>Rl \<Longrightarrow> (Inl l, Inl l') \<in> \<langle>Rl,Rr\<rangle>sum_rel"
    "(r,r')\<in>Rr \<Longrightarrow> (Inr r, Inr r') \<in> \<langle>Rl,Rr\<rangle>sum_rel"
    by simp_all




  (* TODO: Move *)
  lemma pure_assn_eq_false_iff[simp]: "\<up>P = false \<longleftrightarrow> \<not>P" by auto
  lemma pure_assn_eq_emp_iff[simp]: "\<up>P = emp \<longleftrightarrow> P" by (cases P) auto

  lemma pure_rel_eq_false_iff: "pure R x y = false \<longleftrightarrow> (y,x)\<notin>R"
    by (auto simp: pure_def)


  (* TODO: Move to Misc *)
  lemma same_fst_trancl[simp]: "(same_fst P R)\<^sup>+ = same_fst P (\<lambda>x. (R x)\<^sup>+)"
  proof -
    {
      fix x y
      assume "(x,y)\<in>(same_fst P R)\<^sup>+"
      hence "(x,y)\<in>same_fst P (\<lambda>x. (R x)\<^sup>+)"
        by induction (auto simp: same_fst_def)
    } moreover {
      fix f f' x y
      assume "((f,x),(f',y))\<in>same_fst P (\<lambda>x. (R x)\<^sup>+)"
      hence [simp]: "f'=f" "P f" and 1: "(x,y)\<in>(R f)\<^sup>+" by (auto simp: same_fst_def)
      from 1 have "((f,x),(f',y))\<in>(same_fst P R)\<^sup>+"
        apply induction
        subgoal by (rule r_into_trancl) auto
        subgoal by (erule trancl_into_trancl) auto
        done
    } ultimately show ?thesis by auto
  qed


  (* TODO: Move to Misc *)
  lemma nth_append_first[simp]: "i<length l \<Longrightarrow> (l@l')!i = l!i"
    by (simp add: nth_append)

  (* TODO: Move *)
  lemma upt_eq_lel_conv:
    "[l..<h] = is1@i#is2 \<longleftrightarrow> is1 = [l..<i] \<and> is2 = [Suc i..<h] \<and> l\<le>i \<and> i<h"
    apply (rule)
    subgoal
      apply (induction is1 arbitrary: l)
      apply (auto simp: upt_eq_Cons_conv) []
      apply (clarsimp simp: upt_eq_Cons_conv)
      using Suc_le_eq upt_rec by auto
    subgoal by (auto simp: upt_conv_Cons[symmetric])
    done

  (* TODO: Move *)
  lemma drop_takeWhile:
    assumes "i\<le>length (takeWhile P l)"
    shows "drop i (takeWhile P l) = takeWhile P (drop i l)"
    using assms
  proof (induction l arbitrary: i)
    case Nil thus ?case by auto
  next
    case (Cons x l) thus ?case
      by (cases i) auto
  qed

(* TODO: Move *)
lemma less_length_takeWhile_conv: "i < length (takeWhile P l) \<longleftrightarrow> (i<length l \<and> (\<forall>j\<le>i. P (l!j)))"
  apply safe
  subgoal using length_takeWhile_le less_le_trans by blast
  subgoal by (metis dual_order.strict_trans2 nth_mem set_takeWhileD takeWhile_nth)
  subgoal by (meson less_le_trans not_le_imp_less nth_length_takeWhile)
  done

lemma eq_len_takeWhile_conv: "i=length (takeWhile P l)
  \<longleftrightarrow> i\<le>length l \<and> (\<forall>j<i. P (l!j)) \<and> (i<length l \<longrightarrow> \<not>P (l!i))"
  apply safe
  subgoal using length_takeWhile_le less_le_trans by blast
  subgoal by (auto simp: less_length_takeWhile_conv)
  subgoal using nth_length_takeWhile by blast
  subgoal by (metis length_takeWhile_le nth_length_takeWhile order.order_iff_strict)
  subgoal by (metis dual_order.strict_trans2 leI less_length_takeWhile_conv linorder_neqE_nat nth_length_takeWhile)
  done

  (* TODO: Move, check DUP *)
  lemma map_leI[intro?]: "\<lbrakk>\<And>x v. m1 x = Some v \<Longrightarrow> m2 x = Some v\<rbrakk> \<Longrightarrow> m1\<subseteq>\<^sub>mm2"
    unfolding map_le_def by force
  lemma map_leD: "m1\<subseteq>\<^sub>mm2 \<Longrightarrow> m1 k = Some v \<Longrightarrow> m2 k = Some v"
    unfolding map_le_def by force

  (* TODO: Move, List.thy, replace less general map_add_upt? *)
  lemma map_add_upt': "map (\<lambda>i. i + ofs) [a..<b] = [a+ofs..<b + ofs]"
    by (induct b) simp_all

  (* TODO: Move *)
  lemma map_restrict_insert_none_simp: "m x = None \<Longrightarrow> m|`(-insert x s) = m|`(-s)"
    by (auto intro!: ext simp:restrict_map_def)

  (* TODO: Move *)
  lemma eq_f_restr_conv: "s\<subseteq>dom (f A) \<and> A = f A |` (-s) \<longleftrightarrow> A \<subseteq>\<^sub>m f A \<and> s = dom (f A) - dom A"
    apply auto
    subgoal by (metis map_leI restrict_map_eq(2))
    subgoal by (metis ComplD restrict_map_eq(2))
    subgoal by (metis Compl_iff restrict_in)
    subgoal by (force simp: map_le_def restrict_map_def)
    done

  corollary eq_f_restr_ss_eq: "\<lbrakk> s\<subseteq>dom (f A) \<rbrakk> \<Longrightarrow> A = f A |` (-s) \<longleftrightarrow> A \<subseteq>\<^sub>m f A \<and> s = dom (f A) - dom A"
    using eq_f_restr_conv by blast

  lemma set_oo_map_alt: "(set \<circ>\<circ> map) f = (\<lambda>l. f ` set l)" by auto




  lemma eq_or_mem_image_simp[simp]: "{f l |l. l = a \<or> l\<in>B} = insert (f a) {f l|l. l\<in>B}" by blast


  subsection \<open>List Slices\<close>
  text \<open>Based on Lars Hupel's code.\<close>
definition slice :: "nat \<Rightarrow> nat \<Rightarrow> 'a list \<Rightarrow> 'a list" where
"slice from to list = take (to - from) (drop from list)"

lemma slice_len[simp]: "\<lbrakk> from \<le> to; to \<le> length xs \<rbrakk> \<Longrightarrow> length (slice from to xs) = to - from"
unfolding slice_def
by simp

lemma slice_head: "\<lbrakk> from < to; to \<le> length xs \<rbrakk> \<Longrightarrow> hd (slice from to xs) = xs ! from"
unfolding slice_def
proof -
  assume a1: "from < to"
  assume "to \<le> length xs"
  then have "\<And>n. to - (to - n) \<le> length (take to xs)"
    by (metis (no_types) slice_def diff_le_self drop_take length_drop slice_len)
  then show "hd (take (to - from) (drop from xs)) = xs ! from"
    using a1 by (metis diff_diff_cancel drop_take hd_drop_conv_nth leI le_antisym less_or_eq_imp_le nth_take)
qed

lemma slice_eq_bounds_empty[simp]: "slice i i xs = []"
unfolding slice_def by auto

lemma slice_nth: "\<lbrakk> from < to; to \<le> length xs; i < to - from \<rbrakk> \<Longrightarrow> slice from to xs ! i = xs ! (from + i)"
unfolding slice_def
by (induction "to - from" arbitrary: "from" to i) simp+

lemma slice_prepend: "\<lbrakk> i \<le> k; k \<le> length xs \<rbrakk> \<Longrightarrow> let p = length ys in slice i k xs = slice (i + p) (k + p) (ys @ xs)"
unfolding slice_def Let_def
by force

lemma slice_Nil[simp]: "slice begin end [] = []"
  unfolding slice_def by auto

lemma slice_Cons: "slice begin end (x#xs)
  = (if begin=0 \<and> end>0 then x#slice begin (end-1) xs else slice (begin - 1) (end - 1) xs)"
  unfolding slice_def
  by (auto simp: take_Cons' drop_Cons')

lemma slice_complete[simp]: "slice 0 (length xs) xs = xs"
  unfolding slice_def
  by simp




  (* TODO: Move *)
  locale Lattice_Syntax begin
    notation
      bot ("\<bottom>") and
      top ("\<top>") and
      inf  (infixl "\<sqinter>" 70) and
      sup  (infixl "\<squnion>" 65) and
      Inf  ("\<Sqinter>_" [900] 900) and
      Sup  ("\<Squnion>_" [900] 900)

  end

  (* TODO: Move *)
  method repeat_all_new methods m = m;(repeat_all_new \<open>m\<close>)?


  (* TODO: Move *)
  lemma RELATESI: "RELATES R" by (simp add: RELATES_def)


  (* TODO: Move, close to RETURN_SPEC_refine *)
  lemma RETURN_RES_refine:
    assumes "\<exists>x'. (x,x')\<in>R \<and> x'\<in>X"
    shows "RETURN x \<le> \<Down>R (RES X)"
    using assms
    by (auto simp: pw_le_iff refine_pw_simps)

  (* TODO: Move. Use for vcg-rules instead of order_trans! *)
  lemmas SPEC_trans = order_trans[where z="SPEC Postcond" for Postcond, zero_var_indexes]

  (* TODO: Move: Refine_Basic/convenience*)
  lemma refine_IdI: "m \<le> m' \<Longrightarrow> m \<le> \<Down>Id m'" by simp

  lemma map_in_list_rel_conv:
    shows "(l, map \<alpha> l) \<in> \<langle>br \<alpha> I\<rangle>list_rel \<longleftrightarrow> (\<forall>x\<in>set l. I x)"
    by (induction l) (auto simp: in_br_conv)

  lemma list_rel_conv_all_nth:
    "(xs,ys)\<in>\<langle>R\<rangle>list_rel \<longleftrightarrow> (length xs = length ys \<and> (\<forall>i<length ys. (xs!i,ys!i)\<in>R))"
    by (auto simp: list_rel_def list_all2_conv_all_nth)

  lemma list_rel_upt_conv: "([a..<b],[c..<d])\<in>\<langle>R\<rangle>list_rel \<longleftrightarrow>
    b-a = d-c \<and>
    (\<forall>i<d-c. (a+i,c+i)\<in>R)"
    by (auto simp: list_rel_conv_all_nth)



  lemma br_set_rel_alt: "(s',s)\<in>\<langle>br \<alpha> I\<rangle>set_rel \<longleftrightarrow> (s=\<alpha>`s' \<and> (\<forall>x\<in>s'. I x))"
    by (auto simp: set_rel_def br_def)

  lemma br_Image_conv[simp]: "br \<alpha> I `` S = {\<alpha> x | x. x\<in>S \<and> I x}"
    by (auto simp: br_def)

  lemma finite_set_rel_transfer: "\<lbrakk>(s,s')\<in>\<langle>R\<rangle>set_rel; single_valued R; finite s\<rbrakk> \<Longrightarrow> finite s'"
    apply (erule single_valued_as_brE)
    by (auto simp: set_rel_def)


  (* TODO: Move *)
  lemma nres_bind_let_law: "(do { x \<leftarrow> do { let y=v; f y }; g x } :: _ nres)
    = do { let y=v; x\<leftarrow> f y; g x }" by auto

  (* TODO: Move *)
  lemma unused_bind_RES_ne[simp]: "X\<noteq>{} \<Longrightarrow> do { _ \<leftarrow> RES X; m} = m"
    by (auto simp: pw_eq_iff refine_pw_simps)


  (* TODO: Move *)
  lemma sup_leof_iff: "(sup a b \<le>\<^sub>n m) \<longleftrightarrow> (nofail a \<and> nofail b \<longrightarrow> a\<le>\<^sub>nm \<and> b\<le>\<^sub>nm)"
    by (auto simp: pw_leof_iff refine_pw_simps)

  lemma sup_leof_rule[refine_vcg]:
    assumes "\<lbrakk>nofail a; nofail b\<rbrakk> \<Longrightarrow> a\<le>\<^sub>nm"
    assumes "\<lbrakk>nofail a; nofail b\<rbrakk> \<Longrightarrow> b\<le>\<^sub>nm"
    shows "sup a b \<le>\<^sub>n m"
    using assms by (auto simp: pw_leof_iff refine_pw_simps)

    lemma ASSUME_leof_iff: "(ASSUME \<Phi> \<le>\<^sub>n SPEC \<Psi>) \<longleftrightarrow> (\<Phi> \<longrightarrow> \<Psi> ())"
      by (auto simp: pw_leof_iff)

    lemma ASSUME_leof_rule[refine_vcg]:
      assumes "\<Phi> \<Longrightarrow> \<Psi> ()"
      shows "ASSUME \<Phi> \<le>\<^sub>n SPEC \<Psi>"
      using assms
      by (auto simp: ASSUME_leof_iff)


    (* TODO: Move *)
    lemma sup_refine[refine]:
      assumes "ai \<le>\<Down>R a"
      assumes "bi \<le>\<Down>R b"
      shows "sup ai bi \<le>\<Down>R (sup a b)"
      using assms by (auto simp: pw_le_iff refine_pw_simps)

  (* TODO: Move *)
  lemma conc_fun_R_mono:
    assumes "R \<subseteq> R'"
    shows "\<Down>R M \<le> \<Down>R' M"
    using assms
    by (auto simp: pw_le_iff refine_pw_simps)



    (* TODO: Move! *)
    lemma prod_case_refine:
      assumes "(p',p)\<in>R1\<times>\<^sub>rR2"
      assumes "\<And>x1' x2' x1 x2. \<lbrakk> p'=(x1',x2'); p=(x1,x2); (x1',x1)\<in>R1; (x2',x2)\<in>R2\<rbrakk> \<Longrightarrow> f' x1' x2' \<le> \<Down>R (f x1 x2)"
      shows "(case p' of (x1',x2') \<Rightarrow> f' x1' x2') \<le>\<Down>R (case p of (x1,x2) \<Rightarrow> f x1 x2)"
      using assms by (auto split: prod.split)

(* TODO: Move *)
(* TODO: Could we base the whole refine_transfer-stuff on arbitrary relations *)
(* TODO: For enres-breakdown, we had to do antisymmetry, in order to get TR_top.
  What is the general shape of tr-relations for that, such that we could show equality directly?
*)
lemma RECT_transfer_rel:
  assumes [simp]: "trimono F" "trimono F'"
  assumes TR_top[simp]: "\<And>x. tr x top"
  assumes P_start[simp]: "P x x'"
  assumes IS: "\<And>D D' x x'. \<lbrakk> \<And>x x'. P x x' \<Longrightarrow> tr (D x) (D' x'); P x x'; RECT F = D \<rbrakk> \<Longrightarrow> tr (F D x) (F' D' x')"
  shows "tr (RECT F x) (RECT F' x')"
  unfolding RECT_def
  apply auto
  apply (rule flatf_gfp_transfer[where tr=tr and P=P])
  apply (auto simp: trimonoD_flatf_ge)
  apply (rule IS)
  apply (auto simp: RECT_def)
  done

lemma RECT_transfer_rel':
  assumes [simp]: "trimono F" "trimono F'"
  assumes TR_top[simp]: "\<And>x. tr x top"
  assumes P_start[simp]: "P x x'"
  assumes IS: "\<And>D D' x x'. \<lbrakk> \<And>x x'. P x x' \<Longrightarrow> tr (D x) (D' x'); P x x' \<rbrakk> \<Longrightarrow> tr (F D x) (F' D' x')"
  shows "tr (RECT F x) (RECT F' x')"
  using RECT_transfer_rel[where tr=tr and P=P,OF assms(1,2,3,4)] IS by blast



  (* TODO: Move *)
  lemma card_doubleton_eq_2_iff[simp]: "card {a,b} = 2 \<longleftrightarrow> a\<noteq>b" by auto

  lemma in_set_image_conv_nth: "f x \<in> f`set l \<longleftrightarrow> (\<exists>i<length l. f (l!i) = f x)"
    by (auto simp: in_set_conv_nth) (metis image_eqI nth_mem)

  lemma set_image_eq_pointwiseI:
    assumes "length l = length l'"
    assumes "\<And>i. i<length l \<Longrightarrow> f (l!i) = f (l'!i)"
    shows "f`set l = f`set l'"
    using assms
    by (fastforce simp: in_set_conv_nth in_set_image_conv_nth)

  lemma insert_swap_set_eq: "i<length l \<Longrightarrow> insert (l!i) (set (l[i:=x])) = insert x (set l)"
    by (auto simp: in_set_conv_nth nth_list_update split: if_split_asm)


  (* TODO: Move *)
  text \<open>Allows refine-rules to add \<open>RELATES\<close> goals if they introduce hidden relations\<close>
  lemma RELATES_pattern[refine_dref_pattern]: "RELATES R \<Longrightarrow> RELATES R" .
  lemmas [refine_hsimp] = RELATES_def


  subsection \<open>OBTAIN combinator\<close>

  (* TODO: Move. And join with SELECT, and whatever we have there! *)
  definition "OBTAIN P \<equiv> ASSERT (\<exists>x. P x) \<then> SPEC P"
  (* TODO: Move *)
  lemma OBTAIN_nofail[refine_pw_simps]: "nofail (OBTAIN P) \<longleftrightarrow> (\<exists>x. P x)"
    unfolding OBTAIN_def
    by (auto simp: refine_pw_simps)
  lemma OBTAIN_inres[refine_pw_simps]: "inres (OBTAIN P) x \<longleftrightarrow> (\<forall>x. \<not>P x) \<or> P x"
    unfolding OBTAIN_def
    by (auto simp: refine_pw_simps)
  lemma OBTAIN_rule[refine_vcg]: "\<lbrakk> \<exists>x. P x; \<And>x. P x \<Longrightarrow> Q x  \<rbrakk> \<Longrightarrow> OBTAIN P \<le> SPEC Q"
    unfolding OBTAIN_def
    by auto
  lemma OBTAIN_refine_iff: "OBTAIN P \<le>\<Down>R (OBTAIN Q) \<longleftrightarrow> (Ex Q \<longrightarrow> Ex P \<and> Collect P \<subseteq> R\<inverse>``Collect Q)"
    unfolding OBTAIN_def by (auto simp: pw_le_iff refine_pw_simps)

  lemma OBTAIN_refine[refine]:
    assumes "RELATES R"
    assumes "\<And>x. Q x \<Longrightarrow> Ex P"
    assumes "\<And>x y. \<lbrakk>Q x; P y\<rbrakk> \<Longrightarrow> \<exists>x'. (y,x')\<in>R \<and> Q x'"
    shows "OBTAIN P \<le>\<Down>R (OBTAIN Q)"
    using assms unfolding OBTAIN_refine_iff
    by blast

  subsection \<open>SELECT combinator\<close>

  definition "SELECT P \<equiv> if \<exists>x. P x then RES {Some x| x. P x} else RETURN None"
  lemma SELECT_rule[refine_vcg]:
    assumes "\<And>x. P x \<Longrightarrow> Q (Some x)"
    assumes "\<forall>x. \<not>P x \<Longrightarrow> Q None"
    shows "SELECT P \<le> SPEC Q"
    unfolding SELECT_def
    using assms
    by auto

  lemma SELECT_refine_iff: "(SELECT P \<le>\<Down>(\<langle>R\<rangle>option_rel) (SELECT P'))
    \<longleftrightarrow> (
      (Ex P' \<longrightarrow> Ex P) \<and>
      (\<forall>x. P x \<longrightarrow> (\<exists>x'. (x,x')\<in>R \<and> P' x'))
    )"
    by (force simp: SELECT_def pw_le_iff refine_pw_simps)

  lemma SELECT_refine[refine]:
    assumes "RELATES R"
    assumes "\<And>x'. P' x' \<Longrightarrow> \<exists>x. P x"
    assumes "\<And>x. P x \<Longrightarrow> \<exists>x'. (x,x')\<in>R \<and> P' x'"
    shows "SELECT P \<le>\<Down>(\<langle>R\<rangle>option_rel) (SELECT P')"
    unfolding SELECT_refine_iff using assms by blast

  lemma SELECT_as_SPEC: "SELECT P = SPEC (\<lambda>None \<Rightarrow> \<forall>x. \<not>P x | Some x \<Rightarrow> P x)"
    unfolding SELECT_def by (auto simp: pw_eq_iff split: option.split)



(****** FOREACH and nfoldli stuff  *************)

section \<open>FOREACH and nfoldli\<close>
  (* TODO: Move *)
  lemma LIST_FOREACH'_refine: "LIST_FOREACH' tsl' c' f' \<sigma>' \<le> LIST_FOREACH \<Phi> tsl' c' f' \<sigma>'"
    apply (rule refine_IdD)
    unfolding LIST_FOREACH_def LIST_FOREACH'_def
    apply refine_rcg
    apply simp
    apply (rule nfoldli_while)
    done

  lemma LIST_FOREACH'_eq: "LIST_FOREACH (\<lambda>_ _. True) tsl' c' f' \<sigma>' = (LIST_FOREACH' tsl' c' f' \<sigma>')"
    apply (rule antisym)
    subgoal
      apply (rule refine_IdD)
      unfolding LIST_FOREACH_def LIST_FOREACH'_def while_eq_nfoldli[symmetric]
      apply (refine_rcg WHILEIT_refine_new_invar)
      unfolding WHILET_def
      apply (rule WHILEIT_refine_new_invar)

      apply refine_dref_type
      apply vc_solve
      unfolding FOREACH_body_def FOREACH_cond_def
      apply refine_vcg
      apply (auto simp: refine_pw_simps pw_le_iff neq_Nil_conv)
      done
    subgoal by (rule LIST_FOREACH'_refine)
    done

subsection \<open>\<open>nfoldli\<close> Additional Stuff\<close>

    (* TODO: Move *)

    lemma nfoldli_refine[refine]:
      assumes "(li, l) \<in> \<langle>S\<rangle>list_rel"
        and "(si, s) \<in> R"
        and CR: "(ci, c) \<in> R \<rightarrow> bool_rel"
        and [refine]: "\<And>xi x si s. \<lbrakk> (xi,x)\<in>S; (si,s)\<in>R; c s \<rbrakk> \<Longrightarrow> fi xi si \<le> \<Down>R (f x s)"
      shows "nfoldli li ci fi si \<le> \<Down> R (nfoldli l c f s)"
      using assms(1,2)
    proof (induction arbitrary: si s rule: list_rel_induct)
      case Nil thus ?case by simp
    next
      case (Cons xi x li l)
      note [refine] = Cons

      show ?case
        apply (simp split del: if_split)
        apply refine_rcg
        using CR Cons.prems by (auto dest: fun_relD)
    qed

    (* Refine, establishing additional invariant *)
    lemma nfoldli_invar_refine:
      assumes "(li,l)\<in>\<langle>S\<rangle>list_rel"
      assumes "(si,s)\<in>R"
      assumes "I [] li si"
      assumes COND: "\<And>l1i l2i l1 l2 si s. \<lbrakk>
        li=l1i@l2i; l=l1@l2; (l1i,l1)\<in>\<langle>S\<rangle>list_rel; (l2i,l2)\<in>\<langle>S\<rangle>list_rel;
        I l1i l2i si; (si,s)\<in>R\<rbrakk> \<Longrightarrow> (ci si, c s)\<in>bool_rel"
      assumes INV: "\<And>l1i xi l2i si. \<lbrakk>li=l1i@xi#l2i; I l1i (xi#l2i) si\<rbrakk> \<Longrightarrow> fi xi si \<le>\<^sub>n SPEC (I (l1i@[xi]) l2i)"
      assumes STEP: "\<And>l1i xi l2i l1 x l2 si s. \<lbrakk>
        li=l1i@xi#l2i; l=l1@x#l2; (l1i,l1)\<in>\<langle>S\<rangle>list_rel; (xi,x)\<in>S; (l2i,l2)\<in>\<langle>S\<rangle>list_rel;
        I l1i (xi#l2i) si; (si,s)\<in>R\<rbrakk> \<Longrightarrow> fi xi si \<le> \<Down>R (f x s)"
      shows "nfoldli li ci fi si \<le> \<Down>R (nfoldli l c f s)"
    proof -
      {
        have [refine_dref_RELATES]: "RELATES R" "RELATES S" by (auto simp: RELATES_def)

        note [refine del] = nfoldli_refine

        fix l1i l2i l1 l2 si s
        assume "(l2i,l2) \<in> \<langle>S\<rangle>list_rel" "(l1i,l1) \<in> \<langle>S\<rangle>list_rel"
        and "li=l1i@l2i" "l=l1@l2"
        and "(si,s)\<in>R" "I l1i l2i si"
        hence "nfoldli l2i ci fi si \<le> \<Down>R (nfoldli l2 c f s)"
        proof (induction arbitrary: si s l1i l1 rule: list_rel_induct)
          case Nil thus ?case by auto
        next
          case (Cons xi x l2i l2)

          show ?case
            apply (simp split del: if_split)
            apply (refine_rcg bind_refine')
            apply (refine_dref_type)
            subgoal using COND[of l1i "xi#l2i" l1 "x#l2" si s] Cons.prems Cons.hyps by auto
            subgoal apply (rule STEP) using Cons.prems Cons.hyps by auto
            subgoal for si' s'
              thm Cons.IH
              apply (rule Cons.IH[of "l1i@[xi]" "l1@[x]"])
              using Cons.prems Cons.hyps
              apply (auto simp: list_rel_append1) apply force
              using INV[of l1i xi l2i si]
              by (auto simp: pw_leof_iff)
            subgoal using Cons.prems by simp
            done
        qed
      }
      from this[of li l "[]" "[]" si s] assms(1,2,3) show ?thesis by auto
    qed


    lemma nfoldli_leof_rule:
      assumes I0: "I [] l0 \<sigma>0"
      assumes IS: "\<And>x l1 l2 \<sigma>. \<lbrakk> l0=l1@x#l2; I l1 (x#l2) \<sigma>; c \<sigma> \<rbrakk> \<Longrightarrow> f x \<sigma> \<le>\<^sub>n SPEC (I (l1@[x]) l2)"
      assumes FNC: "\<And>l1 l2 \<sigma>. \<lbrakk> l0=l1@l2; I l1 l2 \<sigma>; \<not>c \<sigma> \<rbrakk> \<Longrightarrow> P \<sigma>"
      assumes FC: "\<And>\<sigma>. \<lbrakk> I l0 [] \<sigma>; c \<sigma> \<rbrakk> \<Longrightarrow> P \<sigma>"
      shows "nfoldli l0 c f \<sigma>0 \<le>\<^sub>n SPEC P"
    proof -
      {
        fix l1 l2 \<sigma>
        assume "l0=l1@l2" "I l1 l2 \<sigma>"
        hence "nfoldli l2 c f \<sigma> \<le>\<^sub>n SPEC P"
        proof (induction l2 arbitrary: l1 \<sigma>)
          case Nil thus ?case
            apply simp
            apply (cases "c \<sigma>")
            applyS (rule FC; auto)
            applyS (rule FNC[of l1 "[]"]; auto)
            done
        next
          case (Cons x l2)
          note [refine_vcg] = Cons.IH[of "l1@[x]",THEN leof_trans] IS[of l1 x l2 \<sigma>,THEN leof_trans]

          show ?case
            apply (simp split del: if_split)
            apply refine_vcg
            using Cons.prems FNC by auto
        qed
      } from this[of "[]" l0 \<sigma>0] I0 show ?thesis by auto
    qed

  lemma nfoldli_by_idx_gen:
    shows "nfoldli (drop k l) c f s = nfoldli [k..<length l] c (\<lambda>i s. do {
        ASSERT (i<length l);
        let x = l!i;
        f x s
      }) s"
  proof (cases "k\<le>length l")
    case False thus ?thesis by auto
  next
    case True thus ?thesis
    proof (induction arbitrary: s rule: inc_induct)
      case base thus ?case
        by auto
    next
      case (step k)
      from step.hyps have 1: "drop k l = l!k # drop (Suc k) l"
        by (auto simp: Cons_nth_drop_Suc)
      from step.hyps have 2: "[k..<length l] = k#[Suc k..<length l]"
        by (auto simp: upt_conv_Cons)

      show ?case
        unfolding 1 2
        by (auto simp: step.IH[abs_def] step.hyps)
    qed
  qed



  lemma nfoldli_by_idx:
    "nfoldli l c f s = nfoldli [0..<length l] c (\<lambda>i s. do {
      ASSERT (i<length l);
      let x = l!i;
      f x s
    }) s"
    using nfoldli_by_idx_gen[of 0] by auto

  lemma nfoldli_map_inv:
    assumes "inj g"
    shows "nfoldli l c f = nfoldli (map g l) c (\<lambda>x s. f (the_inv g x) s)"
    using assms
    apply (induction l)
    subgoal by auto
    subgoal by (auto simp: the_inv_f_f)
    done

  lemma nfoldli_shift:
    fixes ofs :: nat
    shows "nfoldli l c f = nfoldli (map (\<lambda>i. i+ofs) l) c (\<lambda>x s. do {ASSERT (x\<ge>ofs); f (x - ofs) s})"
    by (induction l) auto

  lemma nfoldli_foreach_shift:
    shows "nfoldli [a..<b] c f = nfoldli [a+ofs..<b+ofs] c (\<lambda>x s. do{ASSERT(x\<ge>ofs); f (x - ofs) s})"
    using nfoldli_shift[of "[a..<b]" c f ofs]
    by (auto simp: map_add_upt')


  (* TODO: Move. Probably we have this already with FOREACH, or iterator! *)
  lemma member_by_nfoldli: "nfoldli l (\<lambda>f. \<not>f) (\<lambda>y _. RETURN (y=x)) False \<le> SPEC (\<lambda>r. r \<longleftrightarrow> x\<in>set l)"
  proof -
    have "nfoldli l (\<lambda>f. \<not>f) (\<lambda>y _. RETURN (y=x)) s \<le> SPEC (\<lambda>r. r \<longleftrightarrow> s \<or> x\<in>set l)" for s
      apply (induction l arbitrary: s)
      subgoal by auto
      subgoal for a l s
        apply clarsimp
        apply (rule order_trans)
        apply rprems
        by auto
      done
    from this[of False] show ?thesis by auto
  qed




subsection \<open>FOREACH with duplicates\<close>

  definition "FOREACHcd S c f \<sigma> \<equiv> do {
    ASSERT (finite S);
    l \<leftarrow> SPEC (\<lambda>l. set l = S);
    nfoldli l c f \<sigma>
  }"

  lemma FOREACHcd_rule:
    assumes "finite S\<^sub>0"
    assumes I0: "I {} S\<^sub>0 \<sigma>\<^sub>0"
    assumes STEP: "\<And>S1 S2 x \<sigma>. \<lbrakk> S\<^sub>0 = insert x (S1\<union>S2); I S1 (insert x S2) \<sigma>; c \<sigma> \<rbrakk> \<Longrightarrow> f x \<sigma> \<le> SPEC (I (insert x S1) S2)"
    assumes INTR: "\<And>S1 S2 \<sigma>. \<lbrakk> S\<^sub>0 = S1\<union>S2; I S1 S2 \<sigma>; \<not>c \<sigma> \<rbrakk> \<Longrightarrow> \<Phi> \<sigma>"
    assumes COMPL: "\<And>\<sigma>. \<lbrakk> I S\<^sub>0 {} \<sigma>; c \<sigma> \<rbrakk> \<Longrightarrow> \<Phi> \<sigma>"
    shows "FOREACHcd S\<^sub>0 c f \<sigma>\<^sub>0 \<le> SPEC \<Phi>"
    unfolding FOREACHcd_def
    apply refine_vcg
    apply fact
    apply (rule nfoldli_rule[where I = "\<lambda>l1 l2 \<sigma>. I (set l1) (set l2) \<sigma>"])
    subgoal using I0 by auto
    subgoal using STEP by auto
    subgoal using INTR by auto
    subgoal using COMPL by auto
    done

  definition FOREACHcdi
    :: "('a set \<Rightarrow> 'a set \<Rightarrow> 'b \<Rightarrow> bool)
      \<Rightarrow> 'a set \<Rightarrow> ('b \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> 'b \<Rightarrow> 'b nres) \<Rightarrow> 'b \<Rightarrow> 'b nres"
    where
    "FOREACHcdi I \<equiv> FOREACHcd"

  lemma FOREACHcdi_rule[refine_vcg]:
    assumes "finite S\<^sub>0"
    assumes I0: "I {} S\<^sub>0 \<sigma>\<^sub>0"
    assumes STEP: "\<And>S1 S2 x \<sigma>. \<lbrakk> S\<^sub>0 = insert x (S1\<union>S2); I S1 (insert x S2) \<sigma>; c \<sigma> \<rbrakk> \<Longrightarrow> f x \<sigma> \<le> SPEC (I (insert x S1) S2)"
    assumes INTR: "\<And>S1 S2 \<sigma>. \<lbrakk> S\<^sub>0 = S1\<union>S2; I S1 S2 \<sigma>; \<not>c \<sigma> \<rbrakk> \<Longrightarrow> \<Phi> \<sigma>"
    assumes COMPL: "\<And>\<sigma>. \<lbrakk> I S\<^sub>0 {} \<sigma>; c \<sigma> \<rbrakk> \<Longrightarrow> \<Phi> \<sigma>"
    shows "FOREACHcdi I S\<^sub>0 c f \<sigma>\<^sub>0 \<le> SPEC \<Phi>"
    unfolding FOREACHcdi_def
    using assms
    by (rule FOREACHcd_rule)

  lemma FOREACHcd_refine[refine]:
    assumes [simp]: "finite s'"
    assumes S: "(s',s)\<in>\<langle>S\<rangle>set_rel"
    assumes SV: "single_valued S"
    assumes R0: "(\<sigma>',\<sigma>)\<in>R"
    assumes C: "\<And>\<sigma>' \<sigma>. (\<sigma>',\<sigma>)\<in>R \<Longrightarrow> (c' \<sigma>', c \<sigma>)\<in>bool_rel"
    assumes F: "\<And>x' x \<sigma>' \<sigma>. \<lbrakk>(x', x) \<in> S; (\<sigma>', \<sigma>) \<in> R\<rbrakk>
       \<Longrightarrow> f' x' \<sigma>' \<le> \<Down> R (f x \<sigma>)"
    shows "FOREACHcd s' c' f' \<sigma>' \<le> \<Down>R (FOREACHcdi I s c f \<sigma>)"
  proof -
    have [refine_dref_RELATES]: "RELATES S" by (simp add: RELATES_def)

    from SV obtain \<alpha> I where [simp]: "S=br \<alpha> I" by (rule single_valued_as_brE)
    with S have [simp]: "s=\<alpha>`s'" and [simp]: "\<forall>x\<in>s'. I x"
      by (auto simp: br_set_rel_alt)

    show ?thesis
      unfolding FOREACHcd_def FOREACHcdi_def
      apply refine_rcg
      apply refine_dref_type
      subgoal by simp
      subgoal
        apply (auto simp: pw_le_iff refine_pw_simps)
        using S
        apply (rule_tac x="map \<alpha> x" in exI)
        apply (auto simp: map_in_list_rel_conv)
        done
      subgoal using R0 by auto
      subgoal using C by auto
      subgoal using F by auto
      done
  qed

  lemma FOREACHc_refines_FOREACHcd_aux:
    shows "FOREACHc s c f \<sigma> \<le> FOREACHcd s c f \<sigma>"
    unfolding FOREACHc_def FOREACHci_def FOREACHoci_by_LIST_FOREACH LIST_FOREACH'_eq
      LIST_FOREACH'_def FOREACHcd_def it_to_sorted_list_def
    apply (rule refine_IdD)
    apply (refine_rcg)
    apply refine_dref_type
    apply auto
    done

  lemmas FOREACHc_refines_FOREACHcd[refine]
    = order_trans[OF FOREACHc_refines_FOREACHcd_aux FOREACHcd_refine]



  section \<open>Miscellaneous\<close>

  text \<open>Ad-hoc tactic to solve locale subgoals that are similar to existing locale assumptions\<close>
  named_theorems l_asm_rules \<open>Rules to be tried for discharging locale assumptions\<close>

  ML \<open>
    fun try_lasms_hard ctxt = let
      fun try_hard thm =
        CAN' (resolve_tac ctxt [thm]) THEN'
        SOLVED' (Method.insert_tac ctxt [thm] THEN_ALL_NEW SELECT_GOAL (auto_tac ctxt))

      val thms = Named_Theorems.get ctxt @{named_theorems l_asm_rules}

      val try_all = SOLVED' (resolve_tac ctxt thms THEN_ALL_NEW assume_tac ctxt)
      val try_all_hard = FIRST' (map try_hard thms)

    in
      TRY o (FIRST' [try_all, SOLVED' (SELECT_GOAL (auto_tac ctxt)), try_all_hard])
    end
    \<close>

  method_setup try_lasms = \<open>Scan.succeed (fn ctxt => SIMPLE_METHOD' (try_lasms_hard ctxt))\<close>
    \<open>Try to solve assumption similar to theorem in \<open>l_asm_rules\<close>\<close>



    (*
      (Still) ad-hoc hack to remove ghost variables.
      TODO:
        Automate case-splitting
        Declare variables as ghost, and only get rid of assertions and invariants containing declared ghost variables.
          warn if not all ghost variables could be removed!

    *)
    named_theorems_rev remove_ghost_rules \<open>Rules to remove ghost variables\<close>
    ML \<open>
      local
        fun is_no_comb_leq @{mpat (typs) "Trueprop (_\<le>(?t::_ nres))"} = let
          val (_,args) = strip_comb t
          val Ts = map fastype_of args
          fun is_nres_type (Type(@{type_name nres},_)) = true | is_nres_type _ = false
        in
          not (exists (exists_subtype is_nres_type) Ts)
        end
          | is_no_comb_leq _ = false

      in
        fun no_comb_refl_tac ctxt = CONCL_COND' is_no_comb_leq THEN' resolve_tac ctxt @{thms order_refl}
      end

      fun remove_ghost_step_tac ctxt = let
        val thms = Named_Theorems_Rev.get ctxt @{named_theorems_rev remove_ghost_rules}
      in
        resolve_tac ctxt thms ORELSE' match_tac ctxt @{thms conjI impI allI} ORELSE' no_comb_refl_tac ctxt
      end

      fun remove_ghost_tac ctxt = REPEAT_ALL_NEW (remove_ghost_step_tac ctxt)

    \<close>

    lemma bind_removeg[remove_ghost_rules]:
      fixes m m' :: "'a nres"
      shows "\<lbrakk>m\<le>m'; \<And>x. f x \<le> f' x\<rbrakk> \<Longrightarrow> do { x\<leftarrow>m; f x } \<le> do { x\<leftarrow>m'; f' x}"
      by (rule Refine_Basic.bind_mono)

    lemma Let_removeg[remove_ghost_rules]:
      "(\<And>x. f x \<le> f' x) \<Longrightarrow> (let x=t in f x) \<le> (let x=t in f' x)" by simp

    lemma [remove_ghost_rules]:
      assumes "\<And>a b. f a b \<le> f' a b"
      shows "(case p of (a,b) \<Rightarrow> f a b) \<le> (case p of (a,b) \<Rightarrow> f' a b)"
      using assms by (cases p) auto

    lemma [remove_ghost_rules]:
      assumes "fn \<le> fn'" "\<And>v. fv v \<le> fv' v"
      shows "(case x of None \<Rightarrow> fn | Some v \<Rightarrow> fv v) \<le> (case x of None \<Rightarrow> fn' | Some v \<Rightarrow> fv' v)"
      using assms by (auto split: option.split)

    lemma [remove_ghost_rules]:
      "\<lbrakk> t \<le> t'; e \<le> e' \<rbrakk> \<Longrightarrow> (if b then t else e) \<le> (if b then t' else e')"
      by auto


    (* To be manually instantiated, to remove invariants and assertions *)
    lemma FOREACHci_removeg:
      "\<lbrakk>\<And>x s. f x s \<le> f' x s\<rbrakk> \<Longrightarrow> FOREACHc S c f \<sigma> \<le> FOREACHci I S c f' \<sigma>"
      apply (rule refine_IdD)
      apply (refine_rcg inj_on_id)
      by auto

    lemma ASSERT_removeg: "f \<le> f' () \<Longrightarrow> f \<le> ASSERT \<Phi>\<bind>f'" by (cases \<Phi>) auto






(* TODO: Move *)

subsubsection \<open>Sum-Type\<close>

fun sum_assn :: "('ai \<Rightarrow> 'a \<Rightarrow> assn) \<Rightarrow> ('bi \<Rightarrow> 'b \<Rightarrow> assn) \<Rightarrow> ('ai+'bi) \<Rightarrow> ('a+'b) \<Rightarrow> assn" where
  "sum_assn A B (Inl ai) (Inl a) = A ai a"
| "sum_assn A B (Inr bi) (Inr b) = B bi b"
| "sum_assn A B _ _ = false"

lemma sum_assn_pure[safe_constraint_rules]: "\<lbrakk>is_pure A; is_pure B\<rbrakk> \<Longrightarrow> is_pure (sum_assn A B)"
  apply (auto simp: is_pure_iff_pure_assn)
  apply (rename_tac x x')
  apply (case_tac x; case_tac x'; simp add: pure_def)
  done

lemma sum_assn_id[simp]: "sum_assn id_assn id_assn = id_assn"
  apply (intro ext)
  subgoal for x y by (cases x; cases y; simp add: pure_def)
  done

lemma sum_assn_pure_conv[simp]: "sum_assn (pure A) (pure B) = pure (\<langle>A,B\<rangle>sum_rel)"
  apply (intro ext)
  subgoal for a b by (cases a; cases b; auto simp: pure_def)
  done


lemma sum_match_cong[sepref_frame_match_rules]:
  "\<lbrakk>
    \<And>x y. \<lbrakk>e = Inl x; e'=Inl y\<rbrakk> \<Longrightarrow> hn_ctxt A x y \<Longrightarrow>\<^sub>t hn_ctxt A' x y;
    \<And>x y. \<lbrakk>e = Inr x; e'=Inr y\<rbrakk> \<Longrightarrow> hn_ctxt B x y \<Longrightarrow>\<^sub>t hn_ctxt B' x y
  \<rbrakk> \<Longrightarrow> hn_ctxt (sum_assn A B) e e' \<Longrightarrow>\<^sub>t hn_ctxt (sum_assn A' B') e e'"
  by (cases e; cases e'; simp add: hn_ctxt_def entt_star_mono)

lemma enum_merge_cong[sepref_frame_merge_rules]:
  assumes "\<And>x y. \<lbrakk>e=Inl x; e'=Inl y\<rbrakk> \<Longrightarrow> hn_ctxt A x y \<or>\<^sub>A hn_ctxt A' x y \<Longrightarrow>\<^sub>t hn_ctxt Am x y"
  assumes "\<And>x y. \<lbrakk>e=Inr x; e'=Inr y\<rbrakk> \<Longrightarrow> hn_ctxt B x y \<or>\<^sub>A hn_ctxt B' x y \<Longrightarrow>\<^sub>t hn_ctxt Bm x y"
  shows "hn_ctxt (sum_assn A B) e e' \<or>\<^sub>A hn_ctxt (sum_assn A' B') e e' \<Longrightarrow>\<^sub>t hn_ctxt (sum_assn Am Bm) e e'"
  apply (rule entt_disjE)
  apply (rule sum_match_cong)
  apply (rule entt_disjD1[OF assms(1)]; simp)
  apply (rule entt_disjD1[OF assms(2)]; simp)

  apply (rule sum_match_cong)
  apply (rule entt_disjD2[OF assms(1)]; simp)
  apply (rule entt_disjD2[OF assms(2)]; simp)
  done

lemma entt_invalid_sum: "hn_invalid (sum_assn A B) e e' \<Longrightarrow>\<^sub>t hn_ctxt (sum_assn (invalid_assn A) (invalid_assn B)) e e'"
  apply (simp add: hn_ctxt_def invalid_assn_def[abs_def])
  apply (rule enttI)
  apply clarsimp
  apply (cases e; cases e'; auto simp: mod_star_conv pure_def)
  done

lemmas invalid_sum_merge[sepref_frame_merge_rules] = gen_merge_cons[OF entt_invalid_sum]

sepref_register Inr Inl

lemma [sepref_fr_rules]: "(return o Inl,RETURN o Inl) \<in> A\<^sup>d \<rightarrow>\<^sub>a sum_assn A B"
  by sepref_to_hoare sep_auto
lemma [sepref_fr_rules]: "(return o Inr,RETURN o Inr) \<in> B\<^sup>d \<rightarrow>\<^sub>a sum_assn A B"
  by sepref_to_hoare sep_auto

sepref_register case_sum

text \<open>In the monadify phase, this eta-expands to make visible all required arguments\<close>
lemma [sepref_monadify_arity]: "case_sum \<equiv> \<lambda>\<^sub>2f1 f2 x. SP case_sum$(\<lambda>\<^sub>2x. f1$x)$(\<lambda>\<^sub>2x. f2$x)$x"
  by simp

text \<open>This determines an evaluation order for the first-order operands\<close>
lemma [sepref_monadify_comb]: "case_sum$f1$f2$x \<equiv> op \<bind>$(EVAL$x)$(\<lambda>\<^sub>2x. SP case_sum$f1$f2$x)" by simp

text \<open>This enables translation of the case-distinction in a non-monadic context.\<close>
lemma [sepref_monadify_comb]: "EVAL$(case_sum$(\<lambda>\<^sub>2x. f1 x)$(\<lambda>\<^sub>2x. f2 x)$x)
  \<equiv> op \<bind>$(EVAL$x)$(\<lambda>\<^sub>2x. SP case_sum$(\<lambda>\<^sub>2x. EVAL $ f1 x)$(\<lambda>\<^sub>2x. EVAL $ f2 x)$x)"
  apply (rule eq_reflection)
  by (simp split: sum.splits)

text \<open>Auxiliary lemma, to lift simp-rule over \<open>hn_ctxt\<close>\<close>
lemma sum_assn_ctxt: "sum_assn A B x y = z \<Longrightarrow> hn_ctxt (sum_assn A B) x y = z"
  by (simp add: hn_ctxt_def)

text \<open>The cases lemma first extracts the refinement for the datatype from the precondition.
  Next, it generate proof obligations to refine the functions for every case.
  Finally the postconditions of the refinement are merged.

  Note that we handle the
  destructed values separately, to allow reconstruction of the original datatype after the case-expression.

  Moreover, we provide (invalidated) versions of the original compound value to the cases,
  which allows access to pure compound values from inside the case.
  \<close>
lemma sum_cases_hnr:
  fixes A B e e'
  defines [simp]: "INVe \<equiv> hn_invalid (sum_assn A B) e e'"
  assumes FR: "\<Gamma> \<Longrightarrow>\<^sub>t hn_ctxt (sum_assn A B) e e' * F"
  assumes E1: "\<And>x1 x1a. \<lbrakk>e = Inl x1; e' = Inl x1a\<rbrakk> \<Longrightarrow> hn_refine (hn_ctxt A x1 x1a * INVe * F) (f1' x1a) (hn_ctxt A' x1 x1a * hn_ctxt XX1 e e' * \<Gamma>1') R (f1 x1)"
  assumes E2: "\<And>x2 x2a. \<lbrakk>e = Inr x2; e' = Inr x2a\<rbrakk> \<Longrightarrow> hn_refine (hn_ctxt B x2 x2a * INVe * F) (f2' x2a) (hn_ctxt B' x2 x2a * hn_ctxt XX2 e e' * \<Gamma>2') R (f2 x2)"
  assumes MERGE[unfolded hn_ctxt_def]: "\<Gamma>1' \<or>\<^sub>A \<Gamma>2' \<Longrightarrow>\<^sub>t \<Gamma>'"
  shows "hn_refine \<Gamma> (case_sum f1' f2' e') (hn_ctxt (sum_assn A' B') e e' * \<Gamma>') R (case_sum$(\<lambda>\<^sub>2x. f1 x)$(\<lambda>\<^sub>2x. f2 x)$e)"
  apply (rule hn_refine_cons_pre[OF FR])
  apply1 extract_hnr_invalids
  apply (cases e; cases e'; simp add: sum_assn.simps[THEN sum_assn_ctxt])
  subgoal
    apply (rule hn_refine_cons[OF _ E1 _ entt_refl]; assumption?)
    applyS (simp add: hn_ctxt_def) -- \<open>Match precondition for case, get \<open>enum_assn\<close> from assumption generated by \<open>extract_hnr_invalids\<close>\<close>
    apply (rule entt_star_mono) -- \<open>Split postcondition into pairs for compounds and frame, drop \<open>hn_ctxt XX\<close>\<close>
    apply1 (rule entt_fr_drop)
    applyS (simp add: hn_ctxt_def entt_disjI1' entt_disjI2')
    apply1 (rule entt_trans[OF _ MERGE])
    applyS (simp add: entt_disjI1' entt_disjI2')
  done
  subgoal
    apply (rule hn_refine_cons[OF _ E2 _ entt_refl]; assumption?)
    applyS (simp add: hn_ctxt_def)
    apply (rule entt_star_mono)
    apply1 (rule entt_fr_drop)
    applyS (simp add: hn_ctxt_def entt_disjI1' entt_disjI2')
    apply1 (rule entt_trans[OF _ MERGE])
    applyS (simp add: entt_disjI1' entt_disjI2')
  done
done

text \<open>After some more preprocessing (adding extra frame-rules for non-atomic postconditions,
  and splitting the merge-terms into binary merges), this rule can be registered\<close>
lemmas [sepref_comb_rules] = sum_cases_hnr[sepref_prep_comb_rule]

sepref_register isl projl projr
lemma isl_hnr[sepref_fr_rules]: "(return o isl,RETURN o isl) \<in> (sum_assn A B)\<^sup>k \<rightarrow>\<^sub>a bool_assn"
  apply sepref_to_hoare
  subgoal for a b by (cases a; cases b; sep_auto)
  done

lemma projl_hnr[sepref_fr_rules]: "(return o projl,RETURN o projl) \<in> [isl]\<^sub>a (sum_assn A B)\<^sup>d \<rightarrow> A"
  apply sepref_to_hoare
  subgoal for a b by (cases a; cases b; sep_auto)
  done

lemma projr_hnr[sepref_fr_rules]: "(return o projr,RETURN o projr) \<in> [Not o isl]\<^sub>a (sum_assn A B)\<^sup>d \<rightarrow> B"
  apply sepref_to_hoare
  subgoal for a b by (cases a; cases b; sep_auto)
  done


(* TODO: Move. To locale? *)
notation prod_assn (infixr "\<times>\<^sub>a" 70)
notation sum_assn (infixr "+\<^sub>a" 67)

(* TODO: Move *)
text \<open>Setup for string literals\<close>
context fixes x :: "char list" begin
  sepref_register "PR_CONST (STR x)"

  lemma STR_hnr[sepref_import_param]: "(STR x,PR_CONST (STR x))\<in>Id" by simp

end

lemma STR_pat[def_pat_rules]: "STR$x \<equiv> UNPROTECT (STR$x)" by simp

(* TODO: Move *)
lemma nat_param[sepref_import_param]: "(nat,nat) \<in> int_rel \<rightarrow> nat_rel" by auto

(* TODO: Move *)
lemma unit_hnr[sepref_import_param]: "((),())\<in>unit_rel" by auto

lemma int_param[sepref_import_param]: "(int,int) \<in> nat_rel \<rightarrow> int_rel" by auto


(* TODO: Move *)
definition [simp]: "op_ASSUME_bind I m \<equiv> Refine_Basic.bind (ASSUME I) (\<lambda>_. m)"
lemma pat_ASSUME_bind[def_pat_rules]:
  "Refine_Basic.bind$(ASSUME$I)$(\<lambda>\<^sub>2_. m) \<equiv> UNPROTECT (op_ASSUME_bind I)$m"
  by simp

lemma id_op_ASSUME_bind[id_rules]:
  "PR_CONST (op_ASSUME_bind I) ::\<^sub>i TYPE('a nres \<Rightarrow> 'a nres)"
  by simp

lemma arity_ASSUME_bind[sepref_monadify_arity]:
  "PR_CONST (op_ASSUME_bind I) \<equiv> \<lambda>\<^sub>2m. SP (PR_CONST (op_ASSUME_bind I))$m"
  apply (rule eq_reflection)
  by auto

lemma hn_ASSUME_bind[sepref_comb_rules]:
  assumes "vassn_tag \<Gamma> \<Longrightarrow> I"
  assumes "I \<Longrightarrow> hn_refine \<Gamma> c \<Gamma>' R m"
  shows "hn_refine \<Gamma> c \<Gamma>' R (PR_CONST (op_ASSUME_bind I)$m)"
  apply (rule hn_refine_preI)
  using assms
  apply (cases I)
  apply (auto simp: vassn_tag_def)
  done







subsection \<open>Maybe-Head Insertion into Distinct List\<close>
text \<open>
  Insertion into distinct list, where the inserted element is either the head of the list, or
  not contained into the list. Useful to avoid duplicate insertions into the
  literal->clause map.
\<close>

definition "mbhd_invar x l \<equiv> distinct l \<and> x\<notin>set (tl l)"
definition (in -) "mbhd_insert x l \<equiv> if l=[] then [x] else if (x = hd l) then l else x#l"

lemma mbhd_insert_invar: "mbhd_invar x l \<Longrightarrow> mbhd_invar x (mbhd_insert x l)"
  unfolding mbhd_invar_def mbhd_insert_def by (cases l) auto

lemma mbhd_insert_correct: "set (mbhd_insert x l) = insert x (set l)"
  unfolding mbhd_insert_def by auto

lemma mbhd_invar_init: "distinct l \<and> x\<notin>set l \<Longrightarrow> mbhd_invar x l"
  unfolding mbhd_invar_def by (cases l) auto

lemma mbhd_invar_exit: "mbhd_invar x l \<Longrightarrow> distinct l"
  unfolding mbhd_invar_def by (cases l) auto





end
