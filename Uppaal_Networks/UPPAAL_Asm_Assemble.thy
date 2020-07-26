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

fun assemble :: "instr list \<Rightarrow> concrete_program" where
  "assemble listing = CProg
    (\<lambda>pc. if pc < length listing then Some (listing ! pc) else None)"

type_synonym r_prog = "instr list"

fun CPROG :: "r_prog \<Rightarrow> concrete_program" where
  "CPROG p = assemble p"

code_datatype CPROG

lemma[code]: "assemble listing = CPROG listing" by simp

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

lemma[code]: "prog_domain (CPROG listing) = upto (length listing)"
proof(intro Set.equalityI Set.subsetI, goal_cases)
  case (1 x)
  hence "(if x < length listing then Some (listing ! x) else None) \<noteq> None" by (simp add: domIff)
  hence "x < length listing" by presburger
  thus ?case by simp
qed (simp add: domIff)

lemma[code]: "fetch_op (CPROG listing) pc = (if pc < length listing then Some (listing ! pc) else None)" by simp

end