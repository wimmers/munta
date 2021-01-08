theory Abs_List
  imports Main "HOL-Library.Lattice_Syntax"
begin

instantiation list :: (order) order
begin
  fun less_eq_list :: "'a list \<Rightarrow> 'a list \<Rightarrow> bool" where
    "less_eq_list [] _ \<longleftrightarrow> True" |
    "less_eq_list (a # as) (b # bs) \<longleftrightarrow> a \<le> b \<and> as \<le> bs" |
    "less_eq_list (a # as) [] \<longleftrightarrow> False"

  fun less_list :: "'a list \<Rightarrow> 'a list \<Rightarrow> bool" where
    "less_list a b \<longleftrightarrow> a \<le> b \<and> \<not> b \<le> a"

instance proof(standard, goal_cases)
  case (2 x)
  then show ?case by (induction x; simp)
next
  case (3 x y z)
  then show ?case proof(induction x arbitrary: y z)
    case (Cons xa x)
    then show ?case proof(cases y)
      fix ya ys assume y: "y = ya # ys"
      from this Cons show ?thesis proof (cases z)
        fix za zs assume "z = za # zs"
        from this Cons y show ?thesis by auto
      qed simp
    qed simp
  qed simp
next
  case (4 x y)
  then show ?case
  proof (induction x arbitrary: y)
    case Nil then show ?case using less_eq_list.elims(2) by blast
  next
    case (Cons xa xs)
    from this(2) obtain ya ys where "y = ya # ys" using less_eq_list.elims(2) by blast
    from this Cons.prems Cons.IH show ?case using dual_order.antisym by auto
  qed
qed simp
end

instantiation list :: (order) order_bot
begin
definition[simp]: "\<bottom> \<equiv> []"
instance by (standard, simp)
end

instantiation list :: (semilattice_sup) semilattice_sup
begin
  fun sup_list :: "'a list \<Rightarrow> 'a list \<Rightarrow> 'a list" where
    "(a # as) \<squnion> (b # bs) = (a \<squnion> b) # (as \<squnion> bs)" |
    "a \<squnion> [] = a" |
    "[] \<squnion> b = b"

instance proof(standard, goal_cases)
  case (1 x y)
  then show ?case
  proof(induction x arbitrary: y)
    case (Cons a x)
    then show ?case
    proof (cases y)
      fix ya ys assume "y = ya # ys"
      then show ?thesis using Cons by simp
    qed simp
  qed simp
next
  case (2 y x)
  then show ?case
  proof(induction y arbitrary: x)
    case (Cons a y)
    then show ?case
    proof (cases x)
      fix xa xs assume "x = xa # xs"
      then show ?thesis using Cons by simp
    qed simp
  qed simp
next
  case (3 y x z)
  then show ?case
  proof (induction x arbitrary: y z)
    case Nil
    then show ?case by (cases y; cases z; simp)
  next
    case (Cons a x)
    then show ?case by (cases y; cases z; simp)
  qed
qed
end

instantiation list :: (bounded_semilattice_sup_bot) bounded_semilattice_sup_bot begin instance .. end

fun \<gamma>_list :: "('a \<Rightarrow> 'b set) \<Rightarrow> 'a list \<Rightarrow> 'b list set" where
  "\<gamma>_list _ [] = {[]}" |
  "\<gamma>_list \<gamma>_word (a # as) = {l. \<exists>x xs. l = x # xs \<and> x \<in> \<gamma>_word a \<and> xs \<in> \<gamma>_list \<gamma>_word as} \<squnion> {[]}"

lemma mono_gamma_list:
  assumes
    "\<And>x y. (x::'a::order) \<le> y \<Longrightarrow> ((\<gamma>_word x)::'b::order set) \<le> \<gamma>_word y"
  shows "a \<le> b \<Longrightarrow> \<gamma>_list \<gamma>_word a \<le> \<gamma>_list \<gamma>_word b"
proof (induction a arbitrary: b)
  case Nil
  then show ?case by (induction b; simp)
next
  case (Cons ax as)
  from Cons.prems obtain bx bs where "b = bx # bs" using less_eq_list.elims(2) by blast
  from this Cons show ?case using assms by fastforce
qed


end