theory State_Option
imports AbsInt
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

instantiation option :: (type) bot
begin
definition "\<bottom> \<equiv> None"
declare bot_option_def[simp]
instance ..
end

instantiation option :: (top) top
begin
definition "\<top> \<equiv> Some \<top>"
declare top_option_def[simp]
instance ..
end

instantiation option :: (sup) sup
begin
fun sup_option :: "'a option \<Rightarrow> 'a option \<Rightarrow> 'a option" where
  "sup_option None b = b" |
  "sup_option a None = a" |
  "sup_option (Some a) (Some b) = Some (a \<squnion> b)"
instance ..
end

instantiation option :: (inf) inf
begin
fun inf_option :: "'a option \<Rightarrow> 'a option \<Rightarrow> 'a option" where
  "inf_option None _ = None" |
  "inf_option _ None = None" |
  "inf_option (Some a) (Some b) = Some (a \<sqinter> b)"
instance ..
end

instantiation option :: ("{semilattice_sup, order_top}") absstate
begin
instance proof (standard, goal_cases)
  case (1 x y) then show ?case by (cases x; cases y; simp)
next
  case (2 y x) then show ?case by (cases x; cases y; simp)
next
  case (3 y x z) then show ?case by (cases x; cases y; cases z; simp)
next
  case (5 a) then show ?case by (cases a; simp)
qed simp
end

fun \<gamma>_option :: "('a \<Rightarrow> 'b set) \<Rightarrow> 'a option \<Rightarrow> 'b set" where
"\<gamma>_option \<gamma> None = {}" |
"\<gamma>_option \<gamma> (Some a) = \<gamma> a"

end