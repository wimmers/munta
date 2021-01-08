theory State_Smart
  imports Abs_Int Abs_List Toption Stack Abs_Option Abs_Bool Uppaal_Networks.UPPAAL_Asm_Map
begin

type_synonym 'a arstate = "'a list toption"

datatype ('a, 'b) smart_base = Smart 'b "'a arstate" power_bool
type_synonym ('a, 'b) smart = "('a, 'b) smart_base option"

instantiation smart_base :: (absword, absstack) order_top
begin
  definition[simp]: "\<top> \<equiv> Smart \<top> \<top> \<top>"

  fun less_eq_smart_base :: "('a, 'b) smart_base \<Rightarrow> ('a, 'b) smart_base \<Rightarrow> bool" where
    "less_eq_smart_base (Smart astack aregs aflag) (Smart bstack bregs bflag) \<longleftrightarrow> astack \<le> bstack \<and> aregs \<le> bregs \<and> aflag \<le> bflag"

  fun less_smart_base :: "('a, 'b) smart_base \<Rightarrow> ('a, 'b) smart_base \<Rightarrow> bool" where
    "less_smart_base a b \<longleftrightarrow> a \<le> b \<and> \<not> b \<le> a"
instance
proof (standard, goal_cases)
  case (2 x)
  then show ?case using State_Smart.less_eq_smart_base.elims(3) by fastforce
next
  case (3 x y z) then show ?case by (cases x; cases y; cases z; auto)
next
  case (4 x y) then show ?case by (cases x; cases y; auto)
next
  case (5 a) show ?case by (cases a; simp)
qed simp
end

instantiation smart_base :: (absword, absstack) semilattice_sup
begin
  fun sup_smart_base :: "('a, 'b) smart_base \<Rightarrow> ('a, 'b) smart_base \<Rightarrow> ('a, 'b) smart_base" where
    "sup_smart_base (Smart astack aregs aflag) (Smart bstack bregs bflag) =
      Smart (astack \<squnion> bstack) (aregs \<squnion> bregs) (aflag \<squnion> bflag)"
instance
proof (standard, goal_cases)
  case (1 x y) show ?case by (cases x; cases y; simp)
next
  case (2 y x) show ?case by (cases x; cases y; simp)
next
  case (3 y x z) then show ?case by (cases x; cases y; cases z; simp)
qed
end

fun \<gamma>_regs_gen :: "('a \<Rightarrow> int set) \<Rightarrow> 'a arstate \<Rightarrow> rstate set" where
  "\<gamma>_regs_gen \<gamma>_word Top = \<top>" |
  "\<gamma>_regs_gen \<gamma>_word (Minor l) = \<gamma>_list \<gamma>_word l"

text\<open>Lowest abstract register state that contains all configurations of registers up to n.\<close>
definition regs_bounded_top :: "nat \<Rightarrow> 'a::top arstate" where
  "regs_bounded_top n = Minor (replicate n \<top>)"

lemma regs_bounded_top:
  assumes
    "length rs \<le> n"
    "\<gamma>_word \<top> = \<top>"
  shows "rs \<in> \<gamma>_regs_gen \<gamma>_word (regs_bounded_top n)"
using assms(1) proof(induction n arbitrary: rs)
  case 0
  then show ?case unfolding regs_bounded_top_def by simp
next
  case (Suc n)
  have "\<gamma>_regs_gen \<gamma>_word (regs_bounded_top (Suc n)) = \<gamma>_list \<gamma>_word (replicate (Suc n) \<top>)"
    unfolding regs_bounded_top_def by simp
  have "\<dots> = {l. \<exists>x xs. l = x # xs \<and> x \<in> \<gamma>_word \<top> \<and> xs \<in> \<gamma>_list \<gamma>_word (replicate n \<top>)} \<squnion> {[]}" by simp
  moreover have "rs \<in> {l. \<exists>x xs. l = x # xs \<and> x \<in> \<gamma>_word \<top> \<and> xs \<in> \<gamma>_list \<gamma>_word (replicate n \<top>)} \<squnion> {[]}"
  proof (cases rs)
    case (Cons a as)
    hence l: "length as \<le> n" using Suc.prems by simp
    hence "as \<in> \<gamma>_list \<gamma>_word (replicate n \<top>)"
      using Suc.IH[OF l] by (simp add: regs_bounded_top_def)
    moreover have "a \<in> \<gamma>_word \<top>" using assms(2) by simp
    ultimately show ?thesis using Cons by simp
  qed simp
  then show ?case unfolding regs_bounded_top_def by simp
qed

lemma regs_bounded_top_bounded:
  assumes "rs \<in> \<gamma>_regs_gen \<gamma>_word (regs_bounded_top n)"
  shows "length rs \<le> n"
using assms proof (induction n arbitrary: rs)
  case 0
  then show ?case unfolding regs_bounded_top_def by simp
next
  case (Suc n)
  then show ?case
  proof (cases rs)
    case (Cons a as)
    have "rs \<in> \<gamma>_list \<gamma>_word (replicate (Suc n) \<top>)" using Suc.prems by (simp add: regs_bounded_top_def)
    hence "rs \<in> {l. \<exists>x xs. l = x # xs \<and> x \<in> \<gamma>_word \<top> \<and> xs \<in> \<gamma>_list \<gamma>_word (replicate n \<top>)}" using Cons by simp
    hence a: "as \<in> \<gamma>_regs_gen \<gamma>_word (regs_bounded_top n)" unfolding regs_bounded_top_def by (simp add: Cons)
    have "length as \<le> n" using Suc.IH[OF a] .
    then show ?thesis using Cons by simp
  qed simp
qed

fun astore_single :: "'a::absword \<Rightarrow> nat \<Rightarrow> 'a arstate \<Rightarrow> 'a arstate" where
  "astore_single v r Top = Top" |
  "astore_single v r (Minor regs) = Minor (regs[r := (regs ! r) \<squnion> v])"

lemma astore_single_0:
  shows "astore_single av 0 (Minor (a # ar)) = (Minor ((a \<squnion> av) # ar))"
  by simp

interpretation astore_single_folding: folding_idem
  where f = "astore_single av"
  and z = "aregs"
  for aregs
proof (standard, goal_cases)
  case (1 y x)
  then show ?case
  proof (rule ext)
    fix r0 r1 xa
    have "astore_single av r0 (astore_single av r1 xa) = astore_single av r1 (astore_single av r0 xa)"
    proof (cases xa)
      case (Minor regs)
      then show ?thesis
      proof (cases "r0 = r1")
        case False
        let ?r = "(regs[r0 := (regs ! r0) \<squnion> av])[r1 := (regs ! r1) \<squnion> av]"
        let ?l = "(regs[r1 := (regs ! r1) \<squnion> av])[r0 := (regs ! r0) \<squnion> av]"
        from False have r: "astore_single av r1 (astore_single av r0 xa) = Minor ?r" by (simp add: Minor)
        from False have swap: "?r = ?l" by (meson list_update_swap)
        from False have l: "astore_single av r0 (astore_single av r1 xa) = Minor ?l" by (simp add: Minor)
        from r l swap show ?thesis by simp
      qed simp
    qed simp
    thus "(astore_single av r0 \<circ> astore_single av r1) xa = (astore_single av r1 \<circ> astore_single av r0) xa" by simp
  qed
next
  case (2 r)
  then show ?case
  proof (standard, goal_cases)
    case (1 y)
    then show ?case
    proof (cases y)
      case (Minor regs)
      hence "(astore_single av r \<circ> astore_single av r) y = (astore_single av r (Minor (regs[r := (regs ! r) \<squnion> av])))" by simp
      moreover have "astore_single av r (Minor (regs[r := (regs ! r) \<squnion> av])) = (Minor ((regs[r := (regs ! r) \<squnion> av])[r := (regs ! r) \<squnion> av]))"
        by (metis astore_single.simps(2) length_list_update nth_equalityI nth_list_update_eq nth_list_update_neq sup.right_idem)
      moreover have "astore_single av r y = Minor (regs[r := (regs ! r) \<squnion> av])" using Minor by simp
      ultimately show ?thesis by simp
    qed simp
  qed
qed

locale Smart_Base = Abs_Word \<gamma>_word + Abs_Stack \<gamma>_word for \<gamma>_word
begin

definition[simp]: "\<gamma>_regs_list = \<gamma>_list \<gamma>_word"
lemma mono_gamma_regs_list: "a \<le> b \<Longrightarrow> \<gamma>_regs_list a \<le> \<gamma>_regs_list b"
  using mono_gamma by (simp add: mono_gamma_list)

definition[simp]: "\<gamma>_regs \<equiv> \<gamma>_regs_gen \<gamma>_word"

lemma mono_gamma_regs: "a \<le> b \<Longrightarrow> \<gamma>_regs a \<le> \<gamma>_regs b"
proof -
  assume ass: "a \<le> b"
  show "\<gamma>_regs a \<le> \<gamma>_regs b"
  proof (cases a)
    case Top from this ass show ?thesis using less_eq_toption.elims(2) by force
  next
    fix ax assume ax: "a = Minor ax"
    then show ?thesis
    proof (cases b)
      case Top then show ?thesis by simp
    next
      case (Minor bx)
      from this ax show ?thesis using ass mono_gamma_regs_list by simp
    qed
  qed
qed

lemma regs_length:
  assumes "regs \<in> \<gamma>_regs (Minor l)"
  shows "length regs \<le> length l"
using assms proof (induction l arbitrary: regs)
  case (Cons a as)
  from Cons.prems have "regs = [] \<or> (\<exists>x xs. regs = x # xs \<and> x \<in> \<gamma>_word a \<and> xs \<in> \<gamma>_regs_list as)" by auto
  then show ?case using Cons
  proof (safe, goal_cases)
    case 1 then show ?case using Cons.IH by (simp add: le_SucI)
  qed simp
qed simp

lemma regs_cons:
  assumes "a # as \<in> \<gamma>_regs (Minor (la # ls))"
  shows "as \<in> \<gamma>_regs (Minor ls)"
  using assms by simp

fun load :: "('a::absword) arstate \<Rightarrow> reg \<Rightarrow> 'a" where
  "load Top _ = \<top>" |
  "load (Minor l) r = (if r < length l then l ! r else \<bottom>)"

lemma load:
  assumes
    "r < length regs"
    "regs \<in> \<gamma>_regs aregs"
  shows "(regs ! r) \<in> \<gamma>_word (load aregs r)"
proof (cases aregs)
  case (Minor l)
  from this assms(2) have length: "length regs \<le> length l" using regs_length by blast
  from this Minor assms(1) have load: "load aregs r = l ! r" using Minor by auto
  from length assms Minor have "regs ! r \<in> \<gamma>_word (l ! r)"
  proof (induction regs arbitrary: l r aregs)
    case (Cons a regs)
    obtain la ls where lsplit: "l = la # ls"
      by (metis Cons.prems(1) leD length_Cons list.exhaust list.size(3) zero_less_Suc)
    then show ?case
    proof (cases r)
      case 0
      from this have "a # regs \<in> \<gamma>_regs_list (la # ls)" using Cons by (simp add: lsplit)
      hence "a # regs \<in> {l. \<exists>x xs. l = x # xs \<and> x \<in> \<gamma>_word la \<and> xs \<in> \<gamma>_regs_list ls}" by simp
      hence "a \<in> \<gamma>_word la" by blast
      from this 0 lsplit show ?thesis using Cons.prems(2) by auto
    next
      case (Suc rr)
      have length: "length regs \<le> length ls" using Cons.prems(1) lsplit by auto
      have rrlength: "rr < length regs" using Cons.prems(2) Suc by auto
      have "regs \<in> \<gamma>_regs (Minor ls)" using regs_cons Cons.prems(3) Cons.prems(4) lsplit by blast
      from this length rrlength have rr: "regs ! rr \<in> \<gamma>_word (ls ! rr)" using Cons.IH by blast
      from Suc have "(a # regs) ! r = regs ! rr" by simp
      from this rr Suc lsplit show ?thesis using Cons.IH by simp
    qed
  qed simp
  from this load show ?thesis by simp
qed simp

fun store :: "('a::absword) arstate \<Rightarrow> reg \<Rightarrow> 'a \<Rightarrow> 'a arstate" where
  "store Top _ _ = Top" |
  "store (Minor l) r v = Minor (l[r := v])" (* store (Minor l) r v where r \<ge> length l is undefined because we don't need it. *)

fun \<gamma>_smart :: "('a, 'b) smart \<Rightarrow> collect_state set" where
  "\<gamma>_smart None = \<bottom>" |
  "\<gamma>_smart (Some (Smart astack aregs aflag)) = {(stack, rstate, flag, nl). stack \<in> \<gamma>_stack astack \<and> rstate \<in> \<gamma>_regs aregs \<and> flag \<in> \<gamma>_power_bool aflag}"

lemma in_gamma_smartI:
  assumes
    "stack \<in> \<gamma>_stack astack"
    "rstate \<in> \<gamma>_regs aregs"
    "flag \<in> \<gamma>_power_bool aflag"
  shows
    "(stack, rstate, flag, rs) \<in> \<gamma>_smart (Some (Smart astack aregs aflag))"
  using assms by simp

fun pop2 :: "'b \<Rightarrow> ('a * 'a * 'b)" where
  "pop2 stack =
    (let (a, astack) = pop stack;
         (b, bstack) = pop astack
    in (a, b, bstack))"
lemma pop2_stack_correct: "(ca # cb # c) \<in> \<gamma>_stack b \<Longrightarrow> c \<in> \<gamma>_stack (snd (snd (pop2 b)))"
  by (metis (no_types, lifting) Pair_inject case_prod_beta' pop2.elims pop_stack_correct prod.exhaust_sel)

lemma pop2_return_b_correct: "(ca # cb # c) \<in> \<gamma>_stack b \<Longrightarrow> cb \<in> \<gamma>_word (fst (snd (pop2 b)))"
proof -
  assume ass: "(ca # cb # c) \<in> \<gamma>_stack b"
  hence i: "(cb # c) \<in> \<gamma>_stack (snd (pop b))" using pop_stack_correct by simp
  have "snd (pop2 b) = pop (snd (pop b))"
    by (metis (no_types, lifting) case_prod_beta' pop2.elims prod.exhaust_sel snd_conv)
  from this i show "cb \<in> \<gamma>_word (fst (snd (pop2 b)))" using pop_return_correct by auto
qed

lemma pop2_return_a_correct: "(ca # cb # c) \<in> \<gamma>_stack b \<Longrightarrow> ca \<in> \<gamma>_word (fst (pop2 b))"
  by (metis (no_types, lifting) case_prod_beta' fst_conv pop2.elims pop_return_correct)

fun pop2_push :: "('a \<Rightarrow> 'a \<Rightarrow> 'a) \<Rightarrow> 'b \<Rightarrow> 'b" where
  "pop2_push f stack =
    (let (a, b, rstack) = pop2 stack
    in push rstack (f a b))"

lemma[simp]: "pop2_push f stack =
  push (snd (snd (pop2 stack))) (f (fst (pop2 stack)) (fst (snd (pop2 stack))))"
  by (simp add: case_prod_beta)

lemma pop2_push:
  assumes
    "\<And>x y a b. x \<in> \<gamma>_word a \<Longrightarrow> y \<in> \<gamma>_word b \<Longrightarrow> (cop x y) \<in> \<gamma>_word (f a b)"
    "a # b # rcstack \<in> \<gamma>_stack iastack"
  shows "(cop a b) # rcstack \<in> \<gamma>_stack (pop2_push f iastack)"
  apply (simp add: case_prod_beta Let_def)
  using assms by (meson pop_return_correct pop_stack_correct push_correct)

fun cmp_op :: "('a \<Rightarrow> 'a \<Rightarrow> power_bool) \<Rightarrow> addr \<Rightarrow> ('a::absword, 'b::absstack) smart_base \<Rightarrow> ('a, 'b) smart state_map" where
  "cmp_op f pc (Smart stack regs flag) =
    single (Suc pc) (let (a, b, rstack) = pop2 stack
    in (Some (Smart rstack regs (f a b))))"

lemma cmp_op:
  assumes
    "\<And>c d. (if \<forall>x y. x \<in> \<gamma>_word c \<longrightarrow> y \<in> \<gamma>_word d \<longrightarrow> op x y then BTrue
                else if \<exists>x y. x \<in> \<gamma>_word c \<and> y \<in> \<gamma>_word d \<and> op x y then BBoth
                else BFalse) \<le> f c d"
    "(a # b # rstack, icregs, icflag, icrs) \<in> \<gamma>_smart (Some (Smart iastack iaregs iaflag))"
  shows
    "(rstack, icregs, op a b, icrs) \<in> \<gamma>_smart (lookup (cmp_op f ipc (Smart iastack iaregs iaflag)) (Suc ipc))"
proof -
  from assms(2) have istack: "a # b # rstack \<in> \<gamma>_stack iastack" by simp
  from assms(2) have iregs: "icregs \<in> \<gamma>_regs iaregs" by simp
  from assms(2) have iflag: "icflag \<in> \<gamma>_power_bool iaflag" by simp

  let ?oastate = "(Some (Smart (snd (snd (pop2 iastack))) iaregs (f (fst (pop2 iastack)) (fst (snd (pop2 iastack))))))"
  have lookup: "lookup (cmp_op f ipc (Smart iastack iaregs iaflag)) (Suc ipc) = ?oastate" using single_lookup by (metis (mono_tags, lifting) case_prod_beta' cmp_op.simps)

  from istack have ostack: "rstack \<in> \<gamma>_stack (snd (snd (pop2 iastack)))" using pop2_stack_correct by blast
  from assms(1) istack have oflag: "op a b \<in> \<gamma>_power_bool (f (fst (pop2 iastack)) (fst (snd (pop2 iastack))))" using pop2_return_a_correct pop2_return_b_correct mono_gamma_power_bool by fastforce
  from ostack iregs oflag have "(rstack, icregs, op a b, icrs) \<in> \<gamma>_smart ?oastate" by (rule in_gamma_smartI)

  from this lookup show ?thesis by simp
qed

lemma gamma_regs_cons:
  assumes "x # xs \<in> \<gamma>_regs (Minor (a # as))"
  shows "x \<in> \<gamma>_word a"
  using assms by auto

lemma astore_single:
  assumes
    "regs \<in> \<gamma>_regs aregs"
    "v \<in> \<gamma>_word av"
    "r < length regs"
  shows "regs[r := v] \<in> \<gamma>_regs (astore_single av r aregs)"
proof (cases aregs)
  case (Minor aregsl)
  then show ?thesis
  using assms proof (induction aregsl arbitrary: r regs aregs)
    case Nil
    then show ?case by simp
  next
    case (Cons a aregss)
    have "\<exists>x regss. regs = x # regss"
    proof (rule ccontr, goal_cases)
      case 1
      hence "regs = []" using neq_Nil_conv by blast
      then show ?case using Cons(5) by simp
    qed
    then obtain x regss where splitregs: "regs = x # regss" by blast
    have x: "x \<in> \<gamma>_word a" using gamma_regs_cons Cons.prems(1) Cons.prems(2) splitregs by blast
    then show ?case
    proof (cases r)
      case 0
      from 0 have l: "regs[r := v] = v # regss" using splitregs by simp
      from 0 have r: "astore_single av r aregs = (Minor ((a \<squnion> av) # aregss))" using astore_single_0 Cons.prems(1) by blast
      from l r show ?thesis using Cons splitregs
        by (simp; smt Un_iff \<gamma>_regs_gen.simps(2) \<gamma>_regs_list_def \<gamma>_list.simps(2) in_mono mem_Collect_eq mono_gamma regs_cons sup_ge2)
    next
      case (Suc rn)
      have eq: "regss[rn := v] \<in> \<gamma>_regs (Minor (aregss[rn := (aregss ! rn) \<squnion> av]))"
        using Cons.IH Cons.prems(1) Cons.prems(2) Cons.prems(4) Suc splitregs assms(2) by auto
      have l: "regs[r := v] = (x # regss[rn := v])" by (simp add: Suc splitregs)
      have r: "astore_single av r aregs = Minor (a # (aregss[rn := (aregss ! rn) \<squnion> av]))" by (simp add: Cons.prems(1) Suc)
      from eq l r x show ?thesis by simp
    qed
  qed
qed simp

lemma astore_single_keeps:
  assumes "regs \<in> \<gamma>_regs aregs"
  shows "regs \<in> \<gamma>_regs (astore_single av r aregs)"
proof -
  have "aregs \<le> astore_single av r aregs"
  proof (cases aregs)
    case (Minor regs)
    have "regs \<le> regs[r := (regs ! r) \<squnion> av]"
    proof (induction regs arbitrary: r)
      case (Cons a regs)
      then show ?case
      proof (cases r)
        case (Suc rn)
        then show ?thesis by (simp add: Cons.IH)
      qed simp
    qed simp
    then show ?thesis by (simp add: Minor)
  qed simp
  thus ?thesis using assms mono_gamma_regs by blast
qed

fun natset :: "int set \<Rightarrow> nat set" where
  "natset s = nat ` {x. x \<in> s \<and> x \<ge> 0}"

lemma natset:
  assumes
    "x \<ge> 0"
    "x \<in> s"
  shows "nat x \<in> natset s"
  using assms by simp

lemma natset_finite:
  "finite A \<Longrightarrow> finite (natset A)"
  by simp

lemma natset_insert:
  assumes "insert x A = natset rs"
  shows "\<exists>rrs. A = natset rrs"
proof -
  let ?rrs = "int ` A"
  have "A = natset ?rrs"
  proof (intro Set.equalityI Set.subsetI, goal_cases)
    case (1 x)
    hence "int x \<in> int ` A" by blast
    moreover have "int x \<ge> 0" using of_nat_0_le_iff by blast
    ultimately have "nat (int x) \<in> natset (int ` A)" using image_iff by fastforce
    then show ?case by simp
  next
    case (2 x)
    hence "int x \<in> (int ` A)" by auto
    then show ?case by (simp add: image_iff)
  qed
  thus ?thesis ..
qed

fun astore_multi :: "'a::absword \<Rightarrow> nat set \<Rightarrow> 'a arstate \<Rightarrow> 'a arstate" where
  "astore_multi v rs regs = folding.F (astore_single v) regs rs"

fun astore_singleton :: "'a::absword \<Rightarrow> nat \<Rightarrow> 'a arstate \<Rightarrow> 'a arstate" where
  "astore_singleton v r Top = Top" |
  "astore_singleton v r (Minor regs) = Minor (regs[r := v])"

fun astore :: "'a::absword \<Rightarrow> nat set \<Rightarrow> 'a arstate \<Rightarrow> 'a arstate" where
  "astore v rs regs =
    (if is_singleton rs
     then astore_singleton v (the_elem rs) regs
     else astore_multi v rs regs)"

lemma[code]: "astore_multi av (set rs) aregs = fold (astore_single av) rs aregs"
proof -
  show ?thesis
  proof (induction rs)
    case Nil
    then show ?case by simp
  next
    case (Cons a rs)
    hence "astore_single_folding.F av aregs (insert a (set rs)) = astore_single av a (astore_single_folding.F av aregs (set rs))" using astore_single_folding.insert_idem by blast
    then show ?case
      by (metis (mono_tags, lifting) Cons.IH astore_multi.simps astore_single_folding.folding_axioms fold_commute_apply fold_simps(2) folding.comp_fun_commute list.simps(15))
  qed
qed

lemma astore_multi:
  assumes
    "finite rs"
    "r < length regs"
    "r \<in> rs"
    "regs \<in> \<gamma>_regs aregs"
    "v \<in> \<gamma>_word av"
  shows
    "regs[r := v] \<in> \<gamma>_regs (astore_multi av rs aregs)"
proof -
  from assms have
    "finite rs"
    "r < length regs"
    "r \<in> rs"
    "regs \<in> \<gamma>_regs aregs"
    "v \<in> \<gamma>_word av"
    by auto
  thus ?thesis
  proof (induction "rs" arbitrary: r regs v aregs)
    case (insert x A)
    let ?F = "astore_single_folding.F av aregs"
    have astore: "astore_multi av (insert x A) aregs = ?F (insert x A)" by simp
    have bubble: "?F (insert x A) = astore_single av x (?F A)"
      using astore_single_folding.insert insert.hyps(1) insert.hyps(2) by blast

    show ?case
    proof (cases "x = r")
      case True
      have bubble: "astore_multi av (insert x A) aregs = astore_single av r (?F A)" using astore bubble True by simp
      have regs: "regs \<in> \<gamma>_regs (?F A)" using insert.hyps(1)
      proof(induction A)
        case empty then show ?case using insert.prems(3) by auto
      next
        case (insert xx F) then show ?case using astore_single_keeps by simp
      qed

      from regs have astore_bubble: "regs[r := v] \<in> \<gamma>_regs (astore_single av r (?F A))" using astore_single insert.prems by blast
      from astore astore_bubble bubble show ?thesis by simp
    next
      case False
      hence ina: "r \<in> A" using insert by auto
      have "regs[r := v] \<in> \<gamma>_regs (astore_multi av A aregs)"
        using ina insert.IH insert.prems(1) insert.prems(3) insert.prems(4) by blast
      from this have "regs[r := v] \<in> \<gamma>_regs (?F A)" by simp
      then show ?thesis using astore astore_single_keeps bubble by auto
    qed
  qed blast
qed

lemma astore_singleton:
  assumes
    "r < length regs"
    "regs \<in> \<gamma>_regs aregs"
    "v \<in> \<gamma>_word av"
  shows
    "regs[r := v] \<in> \<gamma>_regs (astore_singleton av r aregs)"
proof -
  show ?thesis
  proof (cases aregs)
    case (Minor aregsl)
    then show ?thesis using assms
    proof (induction aregsl arbitrary: r regs aregs)
      case (Cons a aregss)
      obtain x regss where splitregs: "x # regss = regs" by (metis Cons.prems(2) list.exhaust list.size(3) not_less_zero)
      have x: "x \<in> \<gamma>_word a" using Cons.prems(1) Cons.prems(3) gamma_regs_cons splitregs by blast
      show ?case
      proof (cases r)
        case 0
        from 0 have l: "regs[r := v] = v # regss" using splitregs by auto
        from 0 have r: "astore_singleton av r aregs = (Minor (av # aregss))" by (simp add: Cons.prems(1))
        from l r show ?thesis using Cons using splitregs by auto
      next
        case (Suc rn)
        have "regss[rn := v] \<in> \<gamma>_regs (astore_singleton av rn (Minor aregss))" using Cons.IH
          using Cons.prems(1) Cons.prems(2) Cons.prems(3) Suc assms(3) splitregs by auto
        hence eq: "regss[rn := v] \<in> \<gamma>_regs (Minor (aregss[rn := av]))" by simp
        have l: "regs[r := v] = (x # regss[rn := v])" using Suc splitregs by force
        have r: "astore_singleton av r aregs = Minor (a # (aregss[rn := av]))" by (simp add: Cons.prems(1) Cons.prems(2) Suc)
        from eq l r x show ?thesis by simp
      qed
    qed simp
  qed simp
qed

lemma astore:
  assumes
    "finite rs"
    "r < length regs"
    "r \<in> rs"
    "regs \<in> \<gamma>_regs aregs"
    "v \<in> \<gamma>_word av"
  shows
    "regs[r := v] \<in> \<gamma>_regs (astore av rs aregs)"
proof (cases "is_singleton rs")
  case True
  then obtain r where "rs = {r}" by (simp add: is_singleton_the_elem)
  from True this show ?thesis using assms astore_singleton by simp
next
  case False then show ?thesis using assms astore_multi by simp
qed

fun step_smart_base :: "instr \<Rightarrow> addr \<Rightarrow> ('a::absword, 'b::absstack) smart_base \<Rightarrow> ('a, 'b) smart state_map" where
  "step_smart_base NOP pc (Smart stack regs flag)  = single (Suc pc) (Some (Smart stack regs flag))" |

  "step_smart_base (JMPZ target) pc (Smart stack regs BTrue)  = single (Suc pc) (Some (Smart stack regs BTrue))" |
  "step_smart_base (JMPZ target) pc (Smart stack regs BFalse) = single target (Some (Smart stack regs BFalse))" |
  "step_smart_base (JMPZ target) pc (Smart stack regs BBoth)  = deep_merge {(target, Some (Smart stack regs BBoth)), (Suc pc, Some (Smart stack regs BBoth))}" |

  "step_smart_base ADD           pc (Smart stack regs flag)   =
    single (Suc pc) (Some (Smart (pop2_push aplus stack) regs flag))" |

  "step_smart_base NOT           pc (Smart stack regs flag)   = single (Suc pc) (Some (Smart (snd (pop stack)) regs (not flag)))" |

  "step_smart_base AND           pc (Smart stack regs flag)   =
    (let (a, rstack) = pop stack;
         r0 = if contains a 0 then {(Suc pc, Some (Smart rstack regs (and BFalse flag)))} else {};
         r1 = r0 \<union> (if contains a 1 then {(Suc pc, Some (Smart rstack regs (and BTrue flag)))} else {})
     in deep_merge r1)" |

  "step_smart_base LT pc smart = cmp_op lt pc smart" |
  "step_smart_base LE pc smart = cmp_op le pc smart" |
  "step_smart_base EQ pc smart = cmp_op eq pc smart" |

  "step_smart_base (PUSH v)     pc (Smart stack regs flag)    = single (Suc pc) (Some (Smart (push stack (make v)) regs flag))" |
  "step_smart_base POP          pc (Smart stack regs flag)    = single (Suc pc) (Some (Smart (snd (pop stack)) regs flag))" |

  "step_smart_base (LID r)      pc (Smart stack regs flag)    = single (Suc pc) (Some (Smart (push stack (load regs r)) regs flag))" |

  "step_smart_base STORE        pc (Smart stack regs flag) =
    (let (v, r, rstack) = pop2 stack
     in case concretize r of
          Minor rs \<Rightarrow> single (Suc pc) (Some (Smart rstack (astore v (natset rs) regs) flag)) |
          Top \<Rightarrow> \<top>)" |

  "step_smart_base (STOREI r v) pc (Smart stack regs flag) =
    single (Suc pc) (Some (Smart stack (astore_singleton (make v) r regs) flag))" |

  "step_smart_base COPY pc (Smart stack regs flag) =
    single (Suc pc) (Some (Smart (push stack (word_of flag)) regs flag))" |

  "step_smart_base CALL pc (Smart stack regs flag) =
    (case concretize (fst (pop stack)) of
      Minor xs \<Rightarrow> deep_merge ((\<lambda>suc. (suc, Some (Smart (push (snd (pop stack)) (make (int pc))) regs flag))) ` (natset xs)) |
      Top \<Rightarrow> \<top>)" |

  "step_smart_base RETURN pc (Smart stack regs flag) =
    (case concretize (fst (pop stack)) of
      Minor xs \<Rightarrow> deep_merge ((\<lambda>suc. (suc + 1, Some (Smart (snd (pop stack)) regs flag))) ` (natset xs)) |
      Top \<Rightarrow> \<top>)" |

  "step_smart_base HALT pc (Smart _ _ _) = \<bottom>" |

  "step_smart_base (STOREC c d) pc (Smart stack regs flag) =
    (if d = 0
     then single (Suc pc) (Some (Smart stack regs flag))
     else \<bottom>)" |

  "step_smart_base (SETF b) pc (Smart stack regs _) = single (Suc pc) (Some (Smart stack regs (powerup b)))"

fun step_smart :: "('a::absword, 'b::absstack) smart astep" where
  "step_smart _ _ None = \<bottom>" |
  "step_smart op pc (Some a) = step_smart_base op pc a"

lemma gamma_smart_mono:
  assumes "a \<le> b"
  shows "\<gamma>_smart a \<subseteq> \<gamma>_smart b"
proof (intro Set.subsetI)
  fix x assume ass: "x \<in> \<gamma>_smart a"
  from ass obtain astack aregs aflag where asplit: "a = Some (Smart astack aregs aflag)" by (metis \<gamma>_smart.elims empty_iff)
  from this assms obtain bstack bregs bflag where bsplit: "b = Some (Smart bstack bregs bflag)" by (metis \<gamma>_smart.cases less_eq_option_None_is_None)
  from ass obtain stack rstate flag nl where xsplit: "x = (stack, rstate, flag, nl)" using prod_cases4 by blast
  from assms asplit bsplit have fine_le: "astack \<le> bstack" "aregs \<le> bregs" "aflag \<le> bflag" by auto
  from asplit xsplit ass have ain: "stack \<in> \<gamma>_stack astack \<and> rstate \<in> \<gamma>_regs aregs \<and> flag \<in> \<gamma>_power_bool aflag" by simp
  from ain fine_le have regs: "rstate \<in> \<gamma>_regs bregs" using mono_gamma_regs by blast
  from ain fine_le have flag: "flag \<in> \<gamma>_power_bool bflag" using mono_gamma_power_bool by blast
  from ain fine_le have stack: "stack \<in> \<gamma>_stack bstack" using mono_gamma_stack by blast
  from regs flag stack bsplit xsplit show "x \<in> \<gamma>_smart b" by simp
qed

lemma gamma_smart_top: "\<gamma>_smart \<top> = \<top>"
proof -
  have "rstate \<in> \<gamma>_regs \<top>" "flag \<in> \<gamma>_power_bool \<top>" for rstate flag by auto
  moreover have  "\<top> = Some (Smart \<top> \<top> \<top>)" by (simp add: top_option_def)
  moreover have "{(stack, rstate, flag, nl). stack \<in> \<gamma>_stack \<top> \<and> rstate \<in> \<gamma>_regs \<top> \<and> flag \<in> \<gamma>_power_bool \<top>} = \<top>" by auto
  ultimately show ?thesis by (simp add: \<open>\<top> = Some (Smart \<top> \<top> \<top>)\<close>)
qed

lemma gamma_smart_bot: "\<gamma>_smart \<bottom> = \<bottom>"
  by (metis \<gamma>_smart.elims bot.extremum less_eq_option_Some_None)

lemma step_smart_nonbot_correct:
  assumes "ost \<in> lookup (collect_step op ipc (\<gamma>_smart (Some (Smart iastack iaregs iaflag)))) opc"
  shows "ost \<in> \<gamma>_smart (lookup (step_smart op ipc (Some (Smart iastack iaregs iaflag))) opc)"
proof -
  obtain ocstack ocregs ocflag ocrs where ost_split: "ost = (ocstack, ocregs, ocflag, ocrs)" by (rule prod_cases4)

  let ?ists = "\<gamma>_smart (Some (Smart iastack iaregs iaflag))"
  from assms have "\<exists>ist\<in>?ists. step op (ipc, ist) = Some (opc, ost)" by simp
  from this obtain ist where ist_step: "ist \<in> ?ists" "step op (ipc, ist) = Some (opc, ost)" ..
  obtain icstack icregs icflag icrs where ist_split: "ist = (icstack, icregs, icflag, icrs)" by (rule prod_cases4)

  from ist_split ist_step ost_split have ist_split_step:
    "(icstack, icregs, icflag, icrs) \<in> ?ists"
    "step op (ipc, (icstack, icregs, icflag, icrs)) = Some (opc, (ocstack, ocregs, ocflag, ocrs))" by auto

  from ist_step(1) ist_split have ist_props: "icstack \<in> \<gamma>_stack iastack" "icregs \<in> \<gamma>_regs iaregs" "icflag \<in> \<gamma>_power_bool iaflag" by auto

  show ?thesis
  proof (cases op)
    case NOP
    then show ?thesis using ist_split ist_split_step(2) ist_step(1) ost_split by auto
  next
    case (JMPZ target)
    from JMPZ ist_split_step have stack_preserve: "ocstack = icstack" using step_jmpz(1) by blast
    from JMPZ ist_split_step have regs_preserve: "ocregs = icregs" using step_jmpz(2) by blast
    from JMPZ ist_split_step have flag_preserve: "ocflag = icflag" using step_jmpz(3) by blast
    from JMPZ ist_split_step have rs_preserve: "ocrs = icrs" using step_jmpz(4) by blast
    show ?thesis
    proof (cases iaflag)
      case BTrue
      from this have "icflag = True" using ist_props by simp
      from this JMPZ ist_split_step(2) have "opc = Suc ipc" using step_jmpz_true(4) by blast
      from this BTrue JMPZ have "lookup (step_smart op ipc (Some (Smart iastack iaregs iaflag))) opc = Some (Smart iastack iaregs iaflag)" using single_lookup by simp
      then show ?thesis using ist_split flag_preserve ist_step(1) ost_split regs_preserve stack_preserve by simp
    next
      case BFalse
      from this have "icflag = False" using ist_props by simp
      from this JMPZ ist_split_step(2) have "opc = target" using step_jmpz_false(4) by blast
      from this BFalse JMPZ have "lookup (step_smart op ipc (Some (Smart iastack iaregs iaflag))) opc = Some (Smart iastack iaregs iaflag)" using single_lookup by simp
      then show ?thesis using ist_split flag_preserve ist_step(1) ost_split regs_preserve stack_preserve by simp
    next
      case BBoth
      then show ?thesis
      proof (cases icflag)
        case True
        from this JMPZ ist_split_step(2) have "opc = Suc ipc" using step_jmpz_true(4) by (metis(full_types))
        from this BBoth JMPZ have lookup: "Some (Smart iastack iaregs iaflag) \<le> lookup (step_smart op ipc (Some (Smart iastack iaregs iaflag))) opc" using deep_merge_lookup
          by (metis insert_iff step_smart.simps(2) step_smart_base.simps(4))
        have "ost \<in> \<gamma>_smart (Some (Smart iastack iaregs iaflag))" using ist_split flag_preserve ist_step(1) ost_split regs_preserve stack_preserve by simp
        from this lookup show ?thesis using gamma_smart_mono by blast
      next
        case False
        from this JMPZ ist_split_step(2) have "opc = target" using step_jmpz_false(4) by (metis(full_types))
        from this BBoth JMPZ have lookup: "Some (Smart iastack iaregs iaflag) \<le> lookup (step_smart op ipc (Some (Smart iastack iaregs iaflag))) opc" using deep_merge_lookup
          by (metis insert_iff step_smart.simps(2) step_smart_base.simps(4))
        have "ost \<in> \<gamma>_smart (Some (Smart iastack iaregs iaflag))" using ist_split flag_preserve ist_step(1) ost_split regs_preserve stack_preserve by simp
        from this lookup show ?thesis using gamma_smart_mono by blast
      qed
    qed
  next
    case ADD
    hence f1: "step ADD (ipc, icstack, icregs, icflag, icrs) = Some (opc, ocstack, ocregs, ocflag, ocrs)" using ist_split_step(2) by simp
    then have f2: "ocregs = icregs" by (simp add: step_add(2))
    have flag: "ocflag = icflag" using f1 by (simp add: step_add(3))
    from f1 obtain a b rest where stack: "icstack = a # b # rest" "ocstack = (a + b) # rest" using step_add(5) by blast
    let ?oastack = "pop2_push aplus iastack"
    have lookup: "lookup (step_smart op ipc (Some (Smart iastack iaregs iaflag))) opc = (Some (Smart ?oastack iaregs iaflag))"
      using ADD f1 step_add(1) by auto
    have "ocstack \<in> \<gamma>_stack ?oastack" using plus_correct pop2_push stack ist_props(1) by metis
    then show ?thesis using f2 flag ist_props(2) ist_props(3) lookup ost_split by auto
  next
    case NOT
    from NOT ist_split_step have pc: "opc = Suc ipc" using step_not(1) by blast
    from NOT ist_split_step have regs_preserve: "ocregs = icregs" using step_not(2) by blast
    from NOT ist_split_step have flag: "ocflag = (\<not> icflag)" using step_not(3) by blast
    from NOT ist_split_step have rs_preserve: "ocrs = icrs" using step_not(4) by blast
    from NOT ist_split_step obtain ia where pop: "icstack = ia # ocstack" using step_not(5) by blast
    from this have stack: "ocstack \<in> \<gamma>_stack (snd (pop iastack))" using pop_stack_correct ist_props(1) by simp
    have regs: "ocregs \<in> \<gamma>_regs iaregs" using ist_props(2) regs_preserve by auto
    have flag: "ocflag \<in> \<gamma>_power_bool (not iaflag)" using power_bool_not by (simp add: flag ist_props(3))
    from stack regs flag pc show ?thesis by (simp add: NOT ost_split)
  next
    case AND
    have step: "step AND (ipc, icstack, icregs, icflag, icrs) = Some (opc, ocstack, ocregs, ocflag, ocrs)" using AND ist_split_step(2) by blast
    from step have pc: "opc = Suc ipc" by (simp add: step_and(1))
    from step have regs: "ocregs = icregs" by (simp add: step_and(2))
    from step obtain ia where ia: "icstack = ia # ocstack" "ia = 1 \<or> ia = 0" "ocflag = (ia = 1 \<and> icflag)" using step_and(4) by blast

    let ?mergeset = "let (a, rstack) = pop iastack in
      (if contains a 0 then {(Suc ipc, Some (Smart rstack iaregs (and BFalse iaflag)))} else {})
      \<union> (if contains a 1 then {(Suc ipc, Some (Smart rstack iaregs (and BTrue iaflag)))} else {})"

    have step_mergeset: "step_smart op ipc (Some (Smart iastack iaregs iaflag)) = deep_merge ?mergeset"
      by (metis (no_types, lifting) AND step_smart_base.simps(7) case_prod_beta' step_smart.simps(2))

    from ia(2) have "(ocstack, ocregs, ocflag, ocrs) \<in> \<gamma>_smart (lookup (step_smart op ipc (Some (Smart iastack iaregs iaflag))) opc)"
    proof(safe, goal_cases 1 0)
      case 1
      have init: "Some (Smart (snd (pop iastack)) iaregs (and BTrue iaflag)) \<le> lookup (step_smart op ipc (Some (Smart iastack iaregs iaflag))) opc"
      proof -
        from 1 have "contains (fst (pop iastack)) 1" using contains_correct ia(1) ist_props(1) pop_return_correct by blast
        hence "(Suc ipc, Some (Smart (snd (pop iastack)) iaregs (and BTrue iaflag))) \<in> ?mergeset" by auto
        from this show ?thesis using step_mergeset deep_merge_lookup by (metis (no_types, lifting) pc)
      qed

      have "(ocstack, ocregs, ocflag, ocrs) \<in> \<gamma>_smart (Some (Smart (snd (pop iastack)) iaregs (and BTrue iaflag)))"
      proof (rule in_gamma_smartI, goal_cases)
        case 1 then show ?case using ia(1) ist_props(1) pop_stack_correct by blast next
        case 2 then show ?case using ist_props(2) regs by blast next
        case 3 then show ?case by (smt 1 and.simps(1) and.simps(3) and.simps(5) ia(3) ist_props(3) power_bool.exhaust)
      qed
      from this init show ?case using gamma_smart_mono by blast
    next
      case 0
      have init: "Some (Smart (snd (pop iastack)) iaregs (and BFalse iaflag)) \<le> lookup (step_smart op ipc (Some (Smart iastack iaregs iaflag))) opc"
      proof -
        from 0 have "contains (fst (pop iastack)) 0" using contains_correct ia(1) ist_props(1) pop_return_correct by blast
        hence "(Suc ipc, Some (Smart (snd (pop iastack)) iaregs (and BFalse iaflag))) \<in> ?mergeset" by auto
        from this show ?thesis using step_mergeset deep_merge_lookup by (metis (no_types, lifting) pc)
      qed

      have "(ocstack, ocregs, ocflag, ocrs) \<in> \<gamma>_smart (Some (Smart (snd (pop iastack)) iaregs (and BFalse iaflag)))"
      proof (rule in_gamma_smartI, goal_cases)
        case 1 then show ?case using ia(1) ist_props(1) pop_stack_correct by blast next
        case 2 then show ?case using ist_props(2) regs by blast next
        case 3 then show ?case by (simp add: "0" ia(3))
      qed
      from this init show ?case using gamma_smart_mono by blast
    qed
    thus ?thesis using ost_split by simp
  next
    case LT
    from LT ist_step(2) ist_split ost_split have pc: "opc = Suc ipc" using step_lt(1) by simp
    from LT ist_step(2) ist_split ost_split have regs: "ocregs = icregs" using step_lt(2) by simp
    from LT ist_step(2) ist_split ost_split have rs: "ocrs = icrs" using step_lt(3) by simp
    from LT ist_step(2) ist_split ost_split obtain ia ib where stack: "icstack = ia # ib # ocstack \<and> ocflag = (ia < ib)" using step_lt(4) by blast
    hence "(ia # ib # ocstack, icregs, icflag, icrs) \<in> \<gamma>_smart (Some (Smart iastack iaregs iaflag))" using ist_split_step(1) by blast
    hence "(ocstack, icregs, ia < ib, icrs) \<in> \<gamma>_smart (lookup (cmp_op lt ipc (Smart iastack iaregs iaflag)) (Suc ipc))" using cmp_op lt_correct by blast
    from this LT pc stack ost_split regs rs show ?thesis by simp
  next
    case LE
    from LE ist_step(2) ist_split ost_split have pc: "opc = Suc ipc" using step_le(1) by simp
    from LE ist_step(2) ist_split ost_split have regs: "ocregs = icregs" using step_le(2) by simp
    from LE ist_step(2) ist_split ost_split have rs: "ocrs = icrs" using step_le(3) by simp
    from LE ist_step(2) ist_split ost_split obtain ia ib where stack: "icstack = ia # ib # ocstack \<and> ocflag = (ia \<le> ib)" using step_le(4) by blast
    hence "(ia # ib # ocstack, icregs, icflag, icrs) \<in> \<gamma>_smart (Some (Smart iastack iaregs iaflag))" using ist_split_step(1) by blast
    hence "(ocstack, icregs, ia \<le> ib, icrs) \<in> \<gamma>_smart (lookup (cmp_op le ipc (Smart iastack iaregs iaflag)) (Suc ipc))" using cmp_op le_correct by blast
    from this LE pc stack ost_split regs rs show ?thesis by simp
  next
    case EQ
    from EQ ist_step(2) ist_split ost_split have pc: "opc = Suc ipc" using step_eq(1) by simp
    from EQ ist_step(2) ist_split ost_split have regs: "ocregs = icregs" using step_eq(2) by simp
    from EQ ist_step(2) ist_split ost_split have rs: "ocrs = icrs" using step_eq(3) by simp
    from EQ ist_step(2) ist_split ost_split obtain ia ib where stack: "icstack = ia # ib # ocstack \<and> ocflag = (ia = ib)" using step_eq(4) by blast
    hence "(ia # ib # ocstack, icregs, icflag, icrs) \<in> \<gamma>_smart (Some (Smart iastack iaregs iaflag))" using ist_split_step(1) by blast
    hence "(ocstack, icregs, ia = ib, icrs) \<in> \<gamma>_smart (lookup (cmp_op eq ipc (Smart iastack iaregs iaflag)) (Suc ipc))" using cmp_op eq_correct by blast
    from this EQ pc stack ost_split regs rs show ?thesis by simp
  next
    case (PUSH v)
    from PUSH ist_split_step(2) have regs: "ocregs = icregs" using step_push(3) by blast
    from PUSH ist_split_step(2) have flag: "ocflag = icflag" using step_push(4) by blast
    have "v # icstack \<in> \<gamma>_stack (push iastack (make v))" by (meson push_correct ist_props(1) make_correct)
    from this PUSH flag regs show ?thesis using ist_props(2) ist_props(3) ist_split ist_step(2) by auto
  next
    case POP
    from POP ist_split_step(2) have regs: "ocregs = icregs" using step_pop(2) by blast
    from POP ist_split_step(2) have flag: "ocflag = icflag" using step_pop(3) by blast
    from POP ist_split_step(2) obtain v where stack: "v # ocstack = icstack" using step_pop(5) by blast
    from POP regs flag stack show ?thesis using step_pop using ist_props(1) ist_props(2) ist_props(3) ist_split_step(2) ost_split pop_stack_correct by auto
  next
    case (LID r)
    from this ist_split_step(2) have preds: "opc = Suc ipc \<and> ocstack = (icregs ! r) # icstack \<and> ocregs = icregs \<and> ocflag = icflag \<and> ocrs = icrs \<and> r < length icregs" using step_lid by blast
    hence "(icregs ! r) # icstack \<in> \<gamma>_stack (push iastack (load iaregs r))" using load ist_props(1) ist_props(2) push_correct by auto
    from this preds show ?thesis using LID ist_props(2) ist_props(3) ost_split by auto
  next
    case STORE
    from STORE have static: "opc = Suc ipc \<and> ocflag = icflag \<and> ocrs = icrs" using step_store(1) ist_split_step by blast
    from STORE obtain v r where vr: "icstack = v # r # ocstack \<and> nat r < length icregs \<and> r \<ge> 0 \<and> ocregs = icregs[nat r := v]" using step_store(2) ist_split_step by blast

    let ?av = "fst (pop2 iastack)"
    let ?ar = "fst (snd (pop2 iastack))"
    let ?arstack = "snd (snd (pop2 iastack))"
    show ?thesis
    proof (cases "concretize ?ar")
      case (Minor rs)
      let ?smartregs = "astore ?av (natset rs) iaregs"
      let ?smartval = "Some (Smart ?arstack ?smartregs iaflag)"

      have smartval: "lookup (step_smart op ipc (Some (Smart iastack iaregs iaflag))) opc = ?smartval"
      proof -
        let ?smart = "single (Suc ipc) ?smartval"
        have "step_smart op ipc (Some (Smart iastack iaregs iaflag)) =
          (let (v, r, rstack) = pop2 iastack
           in single (Suc ipc) (Some (Smart rstack (astore v (natset rs) iaregs) iaflag)))"
          using Minor by (simp add: case_prod_beta' STORE)
        hence "step_smart op ipc (Some (Smart iastack iaregs iaflag)) = ?smart" unfolding Let_def by (simp add: case_prod_beta')
        thus ?thesis using static by simp
      qed

      have in_smartval: "ost \<in> \<gamma>_smart ?smartval"
      proof -
        have stack: "ocstack \<in> \<gamma>_stack ?arstack" using pop2_stack_correct ist_props(1) vr by blast
        have flag: "ocflag \<in> \<gamma>_power_bool iaflag" using ist_props(3) static by auto

        have "finite (natset rs)" using Minor concretize_finite natset_finite by blast
        moreover have "nat r \<in> natset rs"
        proof -
          have "r \<in> \<gamma>_word ?ar" using ist_props(1) pop2_return_b_correct vr by blast
          hence "r \<in> rs" using concretize_correct Minor by blast
          thus ?thesis by (simp add: vr)
        qed
        moreover have "icregs \<in> \<gamma>_regs iaregs" using ist_props(2) by blast
        moreover have "v \<in> \<gamma>_word ?av" using ist_props(1) pop2_return_a_correct vr by blast
        ultimately have regs: "ocregs \<in> \<gamma>_regs ?smartregs" using astore vr by blast

        from stack regs flag show ?thesis using ost_split by simp
      qed

      from smartval in_smartval show ?thesis by simp
    qed (simp add: case_prod_beta' STORE top_option_def)
  next
    case (STOREI r v)
    hence step: "opc = Suc ipc \<and> ocstack = icstack \<and> ocregs = icregs[r := v] \<and> ocflag = icflag \<and> ocrs = icrs \<and> r < length icregs" using step_storei ist_split_step(2) by blast
    from step have "ocstack \<in> \<gamma>_stack iastack" using ist_props(1) by force
    moreover from step have "icregs[r := v] \<in> \<gamma>_regs (astore_singleton (make v) r iaregs)" using astore_singleton using ist_props(2) make_correct by auto
    moreover from step have "ocflag \<in> \<gamma>_power_bool iaflag" using ist_props(3) by blast
    ultimately have "(ocstack, ocregs, ocflag, ocrs) \<in> \<gamma>_smart (Some (Smart iastack (astore_singleton (make v) r iaregs) iaflag))" using step by simp
    then show ?thesis using step STOREI ost_split by simp
  next
    case COPY
    hence step: "opc = Suc ipc \<and> ocstack = (int_of icflag) # icstack \<and> ocregs = icregs \<and> ocflag = icflag \<and> ocrs = icrs" using step_copy ist_split_step(2) by blast
    have "(ocstack, ocregs, ocflag, ocrs) \<in> \<gamma>_smart (Some (Smart (push iastack (word_of iaflag)) iaregs iaflag))" using step
      by (meson push_correct in_gamma_smartI ist_props(1) ist_props(2) ist_props(3) word_of)
    then show ?thesis by (simp add: COPY local.step ost_split)
  next
    case CALL
    from CALL have step: "ocregs = icregs \<and> ocflag = icflag \<and> ocrs = icrs" using step_call(1) ist_split_step(2) by blast
    from CALL obtain rstack where rstack: "icstack = int opc # rstack \<and> ocstack = int ipc # rstack" using step_call(2) ist_split_step(2) by blast

    let ?ar = "fst (pop iastack)"
    show ?thesis using CALL
    proof (cases "concretize ?ar")
      case (Minor xs)
      let ?dmset = "(\<lambda>suc. (suc, Some (Smart (push (snd (pop iastack)) (make (int ipc))) iaregs iaflag))) ` (natset xs)"

      let ?ast = "Some (Smart (push (snd (pop iastack)) (make (int ipc))) iaregs iaflag)"
      have "int opc \<in> \<gamma>_word (fst (pop iastack))" using ist_props(1) pop_return_correct rstack by blast
      hence "opc \<in> natset xs" by (smt CollectI Minor concretize_correct image_eqI int_nat_eq nat_int natset.elims subsetD)
      hence indmset: "(opc, ?ast) \<in> ?dmset" by blast
      have ost_gamma: "ost \<in> \<gamma>_smart ?ast"
        using push_correct ist_props(1) ist_props(2) ist_props(3) local.step make_correct ost_split pop_stack_correct rstack by fastforce

      let ?dm = "deep_merge ?dmset"
      have indm: "ost \<in> \<gamma>_smart (lookup ?dm opc)" by (smt indmset deep_merge_lookup gamma_smart_mono ost_gamma subsetD)
      have step_smart: "step_smart op ipc (Some (Smart iastack iaregs iaflag)) = ?dm" using Minor CALL by simp
      from step_smart indm  show ?thesis by simp
    qed (simp add: top_option_def)
  next
    case RETURN
    from RETURN have step: "ocregs = icregs \<and> ocflag = icflag \<and> ocrs = icrs \<and> icstack = int (opc - 1) # ocstack \<and> opc > 0"
      using step_return ist_split_step(2) by blast

    let ?ar = "fst (pop iastack)"
    show ?thesis using RETURN
    proof (cases "concretize ?ar")
      case (Minor xs)
      let ?dmset = "(\<lambda>suc. (suc + 1, Some (Smart (snd (pop iastack)) iaregs iaflag))) ` (natset xs)"

      let ?ast = "Some (Smart (snd (pop iastack)) iaregs iaflag)"
      have inpop: "int opc - 1 \<in> \<gamma>_word (fst (pop iastack))" using ist_props(1) int_ops(6) pop_return_correct step by simp
      hence "opc - 1 \<in> natset xs"
      proof -
        have "\<gamma>_word (fst (pop iastack)) \<subseteq> xs" using concretize_correct Minor by blast
        hence "int opc - 1 \<in> xs" using inpop by blast
        moreover have "int opc - 1 \<ge> 0" using step by simp
        ultimately show ?thesis using natset by force
      qed
      hence "((opc - 1) + 1, ?ast) \<in> ?dmset" by blast
      hence indmset: "(opc, ?ast) \<in> ?dmset" using step by simp
      have ost_gamma: "ost \<in> \<gamma>_smart ?ast"
        using in_gamma_smartI ist_props(1) ist_props(2) ist_props(3) local.step ost_split pop_stack_correct by blast

      let ?dm = "deep_merge ?dmset"
      have indm: "ost \<in> \<gamma>_smart (lookup ?dm opc)" by (smt indmset deep_merge_lookup gamma_smart_mono ost_gamma subsetD)
      have step_smart: "step_smart op ipc (Some (Smart iastack iaregs iaflag)) = ?dm" using Minor RETURN by simp
      from step_smart indm  show ?thesis by simp
    qed (simp add: top_option_def)
  next
    case HALT
    then show ?thesis using assms collect_step_halt_succ by blast
  next
    case (STOREC c d)
    hence step: "opc = Suc ipc \<and> ocstack = icstack \<and> ocregs = icregs \<and> ocflag = icflag \<and> ocrs = c # icrs \<and> d = 0" using step_storec ist_split_step(2) by blast
    hence "ost \<in> \<gamma>_smart (Some (Smart iastack iaregs iaflag))" using ist_props ost_split by auto
    then show ?thesis using step STOREC by simp
  next
    case (SETF b)
    hence step: "opc = Suc ipc \<and> ocstack = icstack \<and> ocregs = icregs \<and> ocflag = b \<and> ocrs = icrs" using step_setf ist_split_step(2) by blast
    hence "ost \<in> \<gamma>_smart (Some (Smart iastack iaregs (powerup b)))" using ist_props(1) ist_props(2) ost_split by auto
    from this SETF step show ?thesis by simp
  qed
qed

end

sublocale Smart_Base \<subseteq> Smart: Abs_Int
  where \<gamma> = "\<gamma>_smart"
    and ai_step = step_smart
proof (standard, goal_cases)
  case (1 a b)
  then show ?case by (rule gamma_smart_mono)
next
  case 2 show ?case by (rule gamma_smart_top)
next
  case 3 show ?case by (rule gamma_smart_bot)
next
  case (4 op ipc a pc)
  then show ?case using step_smart_nonbot_correct
  proof (cases "a = \<bottom>")
    case True
    then show ?thesis by (simp add: bot_option_def)
  next
    case False
    have "lookup (collect_step op ipc (\<gamma>_smart (Some (Smart stack regs flag)))) pc
          \<le> \<gamma>_smart (lookup (step_smart op ipc (Some (Smart stack regs flag))) pc)" for stack regs flag
      using step_smart_nonbot_correct by blast
    from this False show ?thesis by (metis \<gamma>_smart.elims bot_option_def)
  qed
next
  case (5 op ipc pc)
  then show ?case by (simp add: bot_option_def)
qed

fun smart_kill_flag :: "('a, 'b) smart \<Rightarrow> ('a, 'b) smart" where
  "smart_kill_flag (Some (Smart stack regs _)) = Some (Smart stack regs BBoth)" |
  "smart_kill_flag None = None"

sublocale Smart_Base \<subseteq> Smart_C: Abs_Int_C
  where \<gamma> = "\<gamma>_smart"
    and ai_step = step_smart
    and kill_flag = smart_kill_flag
proof (standard, goal_cases)
  case (1 st s f rs x)
  from this obtain stack regs flag where x: "x = Some (Smart stack regs flag)"
    by (metis \<gamma>_smart.elims empty_iff)
  moreover from 1 x have "st \<in> \<gamma>_stack stack \<and> s \<in> \<gamma>_regs regs" by simp
  ultimately show ?case by simp
qed

context Smart_Base
begin
abbreviation "ai_loop \<equiv> Smart.ai_loop"
abbreviation "ai_loop_fp \<equiv> Smart.ai_loop_fp"
end

end