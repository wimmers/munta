theory UPPAAL_Asm_Assemble
  imports UPPAAL_Asm
begin

type_synonym addrspace = "addr set"

definition addr_space_complete :: "program \<Rightarrow> addrspace \<Rightarrow> bool" where
  "addr_space_complete prog space \<equiv> \<forall>pc. prog pc \<noteq> None \<longleftrightarrow> pc \<in> space"

datatype concrete_program = CProg program

fun fetch_op :: "concrete_program \<Rightarrow> addr \<Rightarrow> instr option" where
  "fetch_op (CProg p) = p"

fun prog_domain :: "concrete_program \<Rightarrow> addr set" where
  "prog_domain (CProg p) = dom p"

lemma concrete_program_eqI:
  assumes "\<And>pc. fetch_op a pc = fetch_op b pc"
  shows "a = b"
proof -
  obtain pa where pa: "a = CProg pa" using concrete_program.exhaust by blast
  obtain pb where pb: "b = CProg pb" using concrete_program.exhaust by blast
  from assms pa pb have "pa pc = pb pc" for pc by simp
  from this pa pb show ?thesis by (simp add: ext)
qed

fun assemble :: "instr option list \<Rightarrow> concrete_program" where
  "assemble listing = CProg
    (\<lambda>pc. if pc < length listing then listing ! pc else None)"

type_synonym r_prog = "instr option list"

fun CPROG :: "r_prog \<Rightarrow> concrete_program" where
  "CPROG p = assemble p"

code_datatype CPROG

lemma[code]: "assemble listing = CPROG listing" by simp

fun listing_domain :: "r_prog \<Rightarrow> nat \<Rightarrow> nat set" where
  "listing_domain [] _ = {}" |
  "listing_domain ((Some _) # xs) n = insert n (listing_domain xs (Suc n))" |
  "listing_domain (None # xs) n = listing_domain xs (Suc n)"

lemma listing_domain: "listing_domain l n = {i + n |i. i < length l \<and> l ! i \<noteq> None}"
proof (induction l arbitrary: n)
  case (Cons x xs)
  have xs: "listing_domain xs (Suc n) = {i + Suc n |i. i < length xs \<and> xs ! i \<noteq> None}" using Cons by simp
  then show ?case
  proof (cases x)
    case None
    have "{i + Suc n |i. i < length xs \<and> xs ! i \<noteq> None} = {i + n |i. i < length (x # xs) \<and> (x # xs) ! i \<noteq> None}"
    proof (intro Set.equalityI Set.subsetI, goal_cases)
      case (1 v)
      then obtain i where "v = i + Suc n \<and> i < length xs \<and> xs ! i \<noteq> None" by blast
      hence "v = Suc i + n \<and> Suc i < length (x # xs) \<and> (x # xs) ! Suc i \<noteq> None" by simp
      then show ?case by simp
    next
      case (2 v)
      then show ?case
      proof (cases v)
        case 0 then show ?thesis using 2 None by simp
      next
        case (Suc nat)
        from 2 obtain i where "v = i + n \<and> i < length (x # xs) \<and> (x # xs) ! i \<noteq> None" by blast
        then show ?thesis using None less_Suc_eq_0_disj by auto
      qed
    qed
    then show ?thesis using xs None by simp
  next
    case (Some a)
    have "insert n {i + Suc n |i. i < length xs \<and> xs ! i \<noteq> None} = {i + n |i. i < length (x # xs) \<and> (x # xs) ! i \<noteq> None}"
    proof (intro Set.equalityI Set.subsetI, goal_cases)
      case (1 v)
      then show ?case
      proof (cases "v = n")
        case True
        hence "v = 0 + n \<and> 0 < length (x # xs) \<and> (x # xs) ! 0 \<noteq> None" using 1 Some by simp
        then show ?thesis by blast
      next
        case False
        hence "v \<in> {i + Suc n |i. i < length xs \<and> xs ! i \<noteq> None}" using 1 by blast
        then obtain i where "v = i + Suc n \<and> i < length xs \<and> xs ! i \<noteq> None" by blast
        hence "v = Suc i + n \<and> Suc i < length (x # xs) \<and> (x # xs) ! Suc i \<noteq> None" by simp
        then show ?thesis by blast
      qed
    next
      case (2 v)
      then show ?case
      proof (cases "v = n")
        case False
        then obtain i where "v = Suc i + n \<and> Suc i < length (x # xs) \<and> (x # xs) ! Suc i \<noteq> None" using 2 by force
        hence "v = i + Suc n \<and> i < length xs \<and> xs ! i \<noteq> None" by simp
        then show ?thesis by blast
      qed simp
    qed
    then show ?thesis using Some xs by auto
  qed
qed simp

fun upto :: "nat \<Rightarrow> nat set" where
  "upto n = lessThan n"

fun upto_rec :: "nat \<Rightarrow> nat list" where
  "upto_rec 0 = []" |
  "upto_rec (Suc n) = upto_rec n @ [n]"

fun upto_tailrec :: "nat \<Rightarrow> nat list \<Rightarrow> nat list" where
  "upto_tailrec 0 l = l" |
  "upto_tailrec (Suc n) l = upto_tailrec n (n # l)"

lemma upto_tailrec: "upto_tailrec n xs = upto_rec n @ xs"
  by (induction n arbitrary: xs; simp)

lemma lessThan_upto_rec: "lessThan n = set (upto_rec n)"
proof (induction n)
  case (Suc n)
  have l: "lessThan (Suc n) = lessThan n \<union> {n}" using lessThan_Suc by auto
  have r: "set (upto_rec (Suc n)) = set (upto_rec n) \<union> set [n]" by simp
  from l r show ?case using Suc.IH by simp
qed simp

lemma[code]: "upto n = set (upto_tailrec n [])"
  using lessThan_upto_rec upto_tailrec by simp

lemma[code]: "prog_domain (CPROG listing) = listing_domain listing 0"
proof(intro Set.equalityI Set.subsetI, goal_cases)
  case (1 x)
  have "dom (\<lambda>n. if n < length listing then listing ! n else None) = prog_domain (CPROG listing)"
    using CPROG.simps assemble.simps prog_domain.simps by presburger
  then have f1: "x \<in> dom (\<lambda>n. if n < length listing then listing ! n else None)" by (metis "1")
  then have "x < length listing" using domIff by force
  then show ?case using f1 by (simp add: domIff listing_domain)
next
  case (2 x)
  then show ?case using listing_domain by auto
qed

lemma[code]: "fetch_op (CPROG listing) pc = (if pc < length listing then listing ! pc else None)" by simp

end