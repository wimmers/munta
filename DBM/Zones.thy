subsection \<open>Zones and DBMs\<close>
theory Zones
  imports DBM
begin

type_synonym ('c, 't) zone = "('c, 't) cval set"

type_synonym ('c, 't) cval = "'c \<Rightarrow> 't"

definition cval_add :: "('c,'t) cval \<Rightarrow> 't::plus \<Rightarrow> ('c,'t) cval" (infixr "\<oplus>" 64)
where
  "u \<oplus> d = (\<lambda> x. u x + d)"

definition zone_delay :: "('c, ('t::time)) zone \<Rightarrow> ('c, 't) zone"
("_\<^sup>\<up>" [71] 71)
where
  "Z\<^sup>\<up> = {u \<oplus> d|u d. u \<in> Z \<and> d \<ge> (0::'t)}"

fun clock_set :: "'c list \<Rightarrow> 't::time \<Rightarrow> ('c,'t) cval \<Rightarrow> ('c,'t) cval"
where
  "clock_set [] _ u = u" |
  "clock_set (c#cs) t u = (clock_set cs t u)(c:=t)"

abbreviation clock_set_abbrv :: "'c list \<Rightarrow> 't::time \<Rightarrow> ('c,'t) cval \<Rightarrow> ('c,'t) cval"
("[_\<rightarrow>_]_" [65,65,65] 65)
where
  "[r \<rightarrow> t]u \<equiv> clock_set r t u"

definition zone_set :: "('c, 't::time) zone \<Rightarrow> 'c list \<Rightarrow> ('c, 't) zone"
("_\<^bsub>_ \<rightarrow> 0\<^esub>" [71] 71)
where
  "zone_set Z r = {[r \<rightarrow> (0::'t)]u | u . u \<in> Z}"

lemma clock_set_set[simp]:
  "([r\<rightarrow>d]u) c = d" if "c \<in> set r"
  using that by (induction r) auto

lemma clock_set_id[simp]:
  "([r\<rightarrow>d]u) c = u c" if "c \<notin> set r"
  using that by (induction r) auto

definition DBM_zone_repr :: "('t::time) DBM \<Rightarrow> ('c \<Rightarrow> nat) \<Rightarrow> nat \<Rightarrow> ('c, 't :: time) zone"
("[_]\<^bsub>_,_\<^esub>" [72,72,72] 72)
where
  "[M]\<^bsub>v,n\<^esub> = {u . DBM_val_bounded v u M n}"

lemma dbm_entry_val_mono1:
  "dbm_entry_val u (Some c) (Some c') b \<Longrightarrow> b \<preceq> b' \<Longrightarrow> dbm_entry_val u (Some c) (Some c') b'"
proof (induction b, goal_cases)
  case 1 thus ?case using le_dbm_le le_dbm_lt by - (cases b'; fastforce)
next
  case 2 thus ?case using lt_dbm_le lt_dbm_lt by (cases b'; fastforce)
next
  case 3 thus ?case unfolding dbm_le_def by auto
qed

lemma dbm_entry_val_mono2:
  "dbm_entry_val u None (Some c) b \<Longrightarrow> b \<preceq> b' \<Longrightarrow> dbm_entry_val u None (Some c) b'"
proof (induction b, goal_cases)
  case 1 thus ?case using le_dbm_le le_dbm_lt by - (cases b'; fastforce)
next
  case 2 thus ?case using lt_dbm_le lt_dbm_lt by (cases b'; fastforce)
next
  case 3 thus ?case unfolding dbm_le_def by auto
qed

lemma dbm_entry_val_mono3:
  "dbm_entry_val u (Some c) None b \<Longrightarrow> b \<preceq> b' \<Longrightarrow> dbm_entry_val u (Some c) None b'"
proof (induction b, goal_cases)
  case 1 thus ?case using le_dbm_le le_dbm_lt by - (cases b'; fastforce)
next
  case 2 thus ?case using lt_dbm_le lt_dbm_lt by (cases b'; fastforce)
next
  case 3 thus ?case unfolding dbm_le_def by auto
qed

lemmas dbm_entry_val_mono = dbm_entry_val_mono1 dbm_entry_val_mono2 dbm_entry_val_mono3

lemma DBM_le_subset:
  "\<forall> i j. i \<le> n \<longrightarrow> j \<le> n \<longrightarrow> M i j \<preceq> M' i j \<Longrightarrow> u \<in> [M]\<^bsub>v,n\<^esub> \<Longrightarrow> u \<in> [M']\<^bsub>v,n\<^esub>"
proof -
  assume A: "\<forall>i j. i \<le> n \<longrightarrow> j \<le> n \<longrightarrow> M i j \<preceq> M' i j" "u \<in> [M]\<^bsub>v,n\<^esub>"
  hence "DBM_val_bounded v u M n" by (simp add: DBM_zone_repr_def)
  with A(1) have "DBM_val_bounded v u M' n" unfolding DBM_val_bounded_def
  proof (auto, goal_cases)
    case 1 from this(1,2) show ?case unfolding less_eq[symmetric] by fastforce
  next
    case (2 c)
    hence "dbm_entry_val u None (Some c) (M 0 (v c))" "M 0 (v c) \<preceq> M' 0 (v c)" by auto
    thus ?case using dbm_entry_val_mono2 by fast
  next
    case (3 c)
    hence "dbm_entry_val u (Some c) None (M (v c) 0)" "M (v c) 0 \<preceq> M' (v c) 0" by auto
    thus ?case using dbm_entry_val_mono3 by fast
  next
    case (4 c1 c2)
    hence "dbm_entry_val u (Some c1) (Some c2) (M (v c1) (v c2))" "M (v c1) (v c2) \<preceq> M' (v c1) (v c2)"
    by auto
    thus ?case using dbm_entry_val_mono1 by fast
  qed
  thus "u \<in> [M']\<^bsub>v,n\<^esub>" by (simp add: DBM_zone_repr_def)
qed

end