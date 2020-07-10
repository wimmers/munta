theory UPPAAL_Asm_AbsInt_Option
imports UPPAAL_Asm_AbsInt
begin

instantiation option :: (order) order begin
  fun less_eq_option :: "('a::order) option \<Rightarrow> 'a option \<Rightarrow> bool" where
    "less_eq_option None _ \<longleftrightarrow> True" |
    "less_eq_option (Some x) None \<longleftrightarrow> False" |
    "less_eq_option (Some x) (Some y) \<longleftrightarrow> x \<le> y"
  
  fun less_option :: "'a option \<Rightarrow> 'a option \<Rightarrow> bool" where
    "less_option None None \<longleftrightarrow> False" |
    "less_option None (Some x) \<longleftrightarrow> True" |
    "less_option (Some x) None \<longleftrightarrow> False" |
    "less_option (Some x) (Some y) \<longleftrightarrow> x < y"
instance proof
  show "((x::'a option) < y) = (x \<le> y \<and> \<not> y \<le> x)" for x y by (cases x; cases y) auto
  show "(x::'a option) \<le> x" for x by (cases x) auto
  show "(x::'a option) \<le> z" if "x \<le> y" and "y \<le> z" for x y z
    using that by (cases x; cases y; cases z) auto
  show "(x::'a option) = y" if "x \<le> y" and "y \<le> x"for x y
    using that by (cases x; cases y) auto
qed
end

instantiation option :: (absstate) absstate
begin

definition "\<bottom> \<equiv> None"

definition "\<top> \<equiv> Some \<top>"

fun sup_option :: "'a option \<Rightarrow> 'a option \<Rightarrow> 'a option" where
  "sup_option None b = b" |
  "sup_option a None = a" |
  "sup_option (Some a) (Some b) = Some (a \<squnion> b)"

definition "\<Squnion>(A::'a option set) = (if A = {} \<or> A = {\<bottom>} then \<bottom> else Some (\<Squnion>{x. Some x \<in> A}))"

fun inf_option :: "'a option \<Rightarrow> 'a option \<Rightarrow> 'a option" where
  "inf_option None _ = None" |
  "inf_option _ None = None" |
  "inf_option (Some a) (Some b) = Some (a \<sqinter> b)"

definition "\<Sqinter>(A::'a option set) = (if None \<in> A then None else Some (\<Sqinter>{x. Some x \<in> A}))"

instance proof (standard, goal_cases)
  case (1 x y) then show ?case by (cases x; cases y) auto
next
  case (2 x y) then show ?case by (cases x; cases y) auto
next
  case (3 x y z) then show ?case by (cases x; cases y; cases z) auto
next
  case (4 x y) then show ?case by (cases x; cases y) auto
next
  case (5 y x) then show ?case by (cases x; cases y) auto
next
  case (6 y x z) then show ?case by (cases x; cases y; cases z) auto
next
  case (7 x A)
  then show ?case
  proof (cases x)
    case None then show ?thesis using 7 Inf_option_def by auto
  next
    case (Some a) then show ?thesis using 7 Inf_lower Inf_option_def by force
  qed
next
  case (8 A z)
  then show ?case
  proof (cases z)
    case (Some a)
    then show ?thesis using 8 Inf_option_def le_Inf_iff by fastforce
  qed simp
next
  case (9 x A)
  then show ?case
  proof (cases "A = {} \<or> A = {\<bottom>}")
    case True
    then show ?thesis using "9" bot_option_def by auto
  next
    case False
    have "x \<le> Some (\<Squnion>{x. Some x \<in> A})"
    proof(cases x)
      case (Some a)
      then show ?thesis by (metis 9 Sup_upper less_eq_option.simps(3) mem_Collect_eq)
    qed simp
    from False this show ?thesis by (simp add: Sup_option_def)
  qed
next
  case (10 A z)
  then show ?case
  proof (cases "A = {} \<or> A = {\<bottom>}")
    case True
    then show ?thesis by (simp add: Sup_option_def bot_option_def)
  next
    case False
    then show ?thesis
    proof(cases z)
      case None
      then show ?thesis using "10" False bot_option_def dual_order.antisym by fastforce
    next
      case (Some a)
      then show ?thesis by (metis (mono_tags, lifting) "10" False Sup_le_iff UPPAAL_Asm_AbsInt_Option.Sup_option_def less_eq_option.simps(3) mem_Collect_eq)
    qed
  qed
next
  case 11 then show ?case by (simp add: Inf_option_def top_option_def)
next
  case 12
  then show ?case by (simp add: Sup_option_def)
qed
end

fun \<gamma>_option :: "('a \<Rightarrow> 'b set) \<Rightarrow> 'a option \<Rightarrow> 'b set" where
"\<gamma>_option \<gamma> None = {}" |
"\<gamma>_option \<gamma> (Some a) = \<gamma> a"

end