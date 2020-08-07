theory Word_Set
  imports Word Toption State_Smart Stack_Direct
begin

datatype int_set_base = IntSet "int list"
type_synonym int_set = "int_set_base toption"

instantiation int_set_base :: bounded_semilattice_sup_bot
begin
definition less_eq_int_set_base :: "int_set_base \<Rightarrow> int_set_base \<Rightarrow> bool" where
  "less_eq_int_set_base C1 C2 = undefined"

definition less_int_set_base :: "int_set_base \<Rightarrow> int_set_base \<Rightarrow> bool" where
  "less_int_set_base x y = undefined"

definition "\<bottom> = IntSet []"
fun sup_int_set_base :: "int_set_base \<Rightarrow> int_set_base \<Rightarrow> int_set_base" where
  "sup_int_set_base a b = undefined"
instance
proof (standard, goal_cases)
  case (1 x y)
  then show ?case sorry
next
  case (2 x)
  then show ?case sorry
next
  case (3 x y z)
  then show ?case sorry
next
  case (4 x y)
  then show ?case sorry
next
  case (5 x y)
  then show ?case sorry
next
  case (6 y x)
  then show ?case sorry
next
  case (7 y x z)
  then show ?case sorry
next
  case (8 a)
  then show ?case sorry
qed
end

instantiation toption :: (bounded_semilattice_sup_bot) absword
begin
instance ..
end

fun \<gamma>_int_set :: "int_set \<Rightarrow> int set" where
  "\<gamma>_int_set Top = \<top>" |
  "\<gamma>_int_set (Minor (IntSet v)) = set v"

fun int_set_contains :: "int_set \<Rightarrow> int \<Rightarrow> bool" where
  "int_set_contains Top _ = True" |
  "int_set_contains (Minor (IntSet v)) x = (x \<in> set v)"

fun int_set_make :: "int \<Rightarrow> int_set" where
  "int_set_make x = Minor (IntSet [x])"

fun int_set_concretize :: "int_set \<Rightarrow> int set toption" where
  "int_set_concretize (Minor (IntSet v)) = Minor (set v)" |
  "int_set_concretize Top = Top"

fun int_set_aplus :: "int_set \<Rightarrow> int_set \<Rightarrow> int_set" where
  "int_set_aplus (Minor (IntSet a)) (Minor (IntSet b)) = Minor (IntSet (sorted_list_of_set {x. \<exists>xa xb. x = xa + xb \<and> xa \<in> set a \<and> xb \<in> set b}))" |
  "int_set_aplus _ _ = Top"

fun r_int_set_aplus :: "int_set \<Rightarrow> int_set \<Rightarrow> int_set" where
  "r_int_set_aplus (Minor (IntSet a)) (Minor (IntSet b)) = Minor (IntSet (fold (\<lambda>av acc. fold (\<lambda>bv acc. (av + bv) # acc) acc b) [] a))" |
  "r_int_set_aplus _ _ = Top"

lemma[code]: "int_set_aplus = r_int_set_aplus" sorry

fun int_set_lt :: "int_set \<Rightarrow> int_set \<Rightarrow> power_bool" where
  "int_set_lt (Minor (IntSet a)) (Minor (IntSet b)) =
    (if \<forall>xa xb. xa \<in> set a \<longrightarrow> xb \<in> set b \<longrightarrow> xa < xb
     then BTrue
     else if \<forall>xa xb. xa \<in> set a \<longrightarrow> xb \<in> set b \<longrightarrow> xa \<ge> xb
     then BFalse
     else BBoth)" |
  "int_set_lt Top _ = BBoth" |
  "int_set_lt _ Top = BBoth"

lemma[code]: "int_set_lt = undefined" sorry

fun int_set_le :: "int_set \<Rightarrow> int_set \<Rightarrow> power_bool" where
  "int_set_le (Minor (IntSet a)) (Minor (IntSet b)) =
    (if \<forall>xa xb. xa \<in> set a \<longrightarrow> xb \<in> set b \<longrightarrow> xa \<le> xb
     then BTrue
     else if \<forall>xa xb. xa \<in> set a \<longrightarrow> xb \<in> set b \<longrightarrow> xa > xb
     then BFalse
     else BBoth)" |
  "int_set_le Top _ = BBoth" |
  "int_set_le _ Top = BBoth"

lemma[code]: "int_set_le = undefined" sorry

fun int_set_eq :: "int_set \<Rightarrow> int_set \<Rightarrow> power_bool" where
  "int_set_eq (Minor (IntSet [xa])) (Minor (IntSet [xb])) = powerup (xa = xb)" |
  "int_set_eq (Minor (IntSet a)) (Minor (IntSet b)) =
    (if \<exists>x. x \<in> set a \<and> x \<in> set b
     then BBoth
     else BFalse)" |
  "int_set_eq Top _ = BBoth" |
  "int_set_eq _ Top = BBoth"

lemma[code]: "int_set_eq = undefined" sorry

global_interpretation WordSet: AbsWord
  where \<gamma>_word = \<gamma>_int_set
    and contains = int_set_contains
    and make = int_set_make
    and concretize = int_set_concretize
    and aplus = int_set_aplus
    and lt = int_set_lt
    and le = int_set_le
    and eq = int_set_eq
  defines word_set_loop = WordSet.ai_loop
proof (goal_cases)
  case 1
  then show ?case
  proof (standard, goal_cases)
    case (1 a b)
    then show ?case sorry
  next
    case 2
    then show ?case sorry
  next
    case (3 a x)
    then show ?case sorry
  next
    case (4 v)
    then show ?case sorry
  next
    case (5 a vs)
    then show ?case sorry
  next
    case (6 a vs)
    then show ?case sorry
  next
    case (7 x a y b)
    then show ?case sorry
  next
    case (8 a b)
    then show ?case sorry
  next
    case (9 a b)
    then show ?case sorry
  next
    case (10 a b)
    then show ?case sorry
  qed
qed

end