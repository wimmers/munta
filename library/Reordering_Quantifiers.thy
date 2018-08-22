theory Reordering_Quantifiers
  imports Main
begin

lemma
  assumes A: "finite A"
  shows "finite {(a,b,c) | a b c. a \<in> A \<and> b < (n :: nat) \<and> P c}"
  using assms [[simproc add: finite_Collect]] apply simp
  oops

lemma
  assumes A: "finite A"
  shows "finite {(d, c, a, b) | a b c d. d < n \<and> P c \<and> (a, b) \<in> A}"
  using assms
  using [[simproc add: finite_Collect]] apply simp
  oops
  
  thm Finite_Set.finite_Collect_bounded_ex
lemma rewr:
    "\<exists>x. P1 \<and> Q1 x \<equiv> P1 \<and> (\<exists>x. Q1 x)"
  by simp

lemma
  "finite {x . x \<in> A}" if "finite A"
  using [[simp_trace]]
  using that by simp

lemma
  fixes n :: nat
  assumes A: "finite A"
  shows "finite {t. \<exists> a c. a \<in> A \<and> c < n \<and> t = (a,c)}"
  apply simp
  using assms by simp

lemma
  fixes n :: nat
  assumes A: "finite A"
  shows "finite {(a, c). a \<in> A \<and> c < n}"
  apply simp
  using assms by simp

(* Printing util *)
ML \<open>
  fun pretty_cterm ctxt ctm = Syntax.pretty_term ctxt (Thm.term_of ctm)
  val string_of_cterm = Pretty.string_of oo pretty_cterm
  val string_of_term = Pretty.string_of oo Syntax.pretty_term
\<close>

ML_val \<open>tracing (Syntax.string_of_term @{context} @{term "a < b"})\<close>

ML_val \<open>tracing (ML_Syntax.print_term @{term "a < b"})\<close>

ML \<open>
  fun strip_prop (Const (@{const_name HOL.Trueprop}, _) $ t) = t
    | strip_prop t = t
\<close>

declare [[ML_print_depth = 50]]

ML \<open>
  signature QUANTIFIER1_DATA =
sig
  (*functionality*)
  (*terms to be moved around*)
  (*arguments: preceding quantifies, term under question, preceding terms*)
  val move: (term * string * typ) list -> term -> term list -> bool
  (*always move? if false then moves appear if a non-mover was encountered before*)
  val force_move: bool
  (*rotate quantifiers after moving*)
  val rotate: bool
  (*abstract syntax*)
  val dest_eq: term -> (term * term) option
  val dest_conj: term -> (term * term) option
  val dest_imp: term -> (term * term) option
  val conj: term
  val imp: term
  (*rules*)
  val iff_reflection: thm (* P <-> Q ==> P == Q *)
  val iffI: thm
  val iff_trans: thm
  val conjI: thm
  val conjE: thm
  val impI: thm
  val mp: thm
  val exI: thm
  val exE: thm
  val uncurry: thm (* P --> Q --> R ==> P & Q --> R *)
  val iff_allI: thm (* !!x. P x <-> Q x ==> (!x. P x) = (!x. Q x) *)
  val iff_exI: thm (* !!x. P x <-> Q x ==> (? x. P x) = (? x. Q x) *)
  val all_comm: thm (* (!x y. P x y) = (!y x. P x y) *)
  val ex_comm: thm (* (? x y. P x y) = (? y x. P x y) *)
end;

signature QUANTIFIER1 =
sig
  val prove_one_point_all_tac: Proof.context -> tactic
  val prove_one_point_ex_tac: Proof.context -> tactic
  val rearrange_all: Proof.context -> cterm -> thm option
  (* XXX Need to export this ?*)
  val rearrange_ex': Proof.context -> term -> thm option
  val rearrange_ex: Proof.context -> cterm -> thm option
  val rotate_ex: Proof.context -> cterm -> thm option
  val miniscope_ex: Proof.context -> cterm -> thm option
  val rotate_all: Proof.context -> cterm -> thm option
  val rearrange_ball: (Proof.context -> tactic) -> Proof.context -> cterm -> thm option
  val rearrange_bex: (Proof.context -> tactic) -> Proof.context -> cterm -> thm option
  val rearrange_Collect: (Proof.context -> tactic) -> Proof.context -> cterm -> thm option
end;

functor Quantifier(Data: QUANTIFIER1_DATA): QUANTIFIER1 =
struct

fun extract_conj trms fst xs t =
  (case Data.dest_conj t of
    NONE => NONE
  | SOME (P, Q) =>
      let
        val mover = Data.move xs P trms
      in
        if Data.force_move andalso mover then (if fst then NONE else SOME (xs, P, Q))
        else if Data.force_move andalso Data.move xs Q (P :: trms) then SOME (xs, Q, P)
        else if mover andalso not fst then SOME (xs, P, Q)
        else if
          not Data.force_move andalso (not mover orelse not fst) andalso Data.move xs Q (P :: trms)
          then SOME (xs, Q, P)
        else
          (case extract_conj trms (if Data.force_move then false else fst) xs P of
            SOME (xs, eq, P') => SOME (xs, eq, Data.conj $ P' $ Q)
          | NONE =>
              (case extract_conj (P :: trms)
                    (if Data.force_move then false else (fst andalso mover)) xs Q
               of
                SOME (xs, eq, Q') => SOME (xs, eq, Data.conj $ P $ Q')
              | NONE => NONE))
      end);
(* XXX This is not regularized with respect to term context *)
fun extract_imp fst xs t =
  (case Data.dest_imp t of
    NONE => NONE
  | SOME (P, Q) =>
      if Data.move xs P [] then (if fst then NONE else SOME (xs, P, Q))
      else
        (case extract_conj [] false xs P of
          SOME (xs, eq, P') => SOME (xs, eq, Data.imp $ P' $ Q)
        | NONE =>
            (case extract_imp false xs Q of
              NONE => NONE
            | SOME (xs, eq, Q') => SOME (xs, eq, Data.imp $ P $ Q'))));

fun extract_quant extract q =
  let
    fun exqu xs ((qC as Const (qa, _)) $ Abs (x, T, Q)) =
          if qa = q then exqu ((qC, x, T) :: xs) Q else NONE
      | exqu xs P = extract (if Data.force_move then null xs else true) xs P
  in exqu [] end;

fun prove_conv ctxt tu tac =
  let
    val (goal, ctxt') =
      yield_singleton (Variable.import_terms true) (Logic.mk_equals tu) ctxt;
    val thm =
      Goal.prove ctxt' [] [] goal
        (fn {context = ctxt'', ...} =>
          resolve_tac ctxt'' [Data.iff_reflection] 1 THEN tac ctxt'');
  in singleton (Variable.export ctxt' ctxt) thm end;

fun maybe_tac tac = if Data.rotate then tac else K all_tac;

fun qcomm_tac ctxt qcomm qI i =
  REPEAT_DETERM (maybe_tac (resolve_tac ctxt [qcomm]) i THEN resolve_tac ctxt [qI] i);

(* Proves (? x0..xn. ... & x0 = t & ...) = (? x1..xn x0. x0 = t & ... & ...)
   Better: instantiate exI
*)
local
  val excomm = Data.ex_comm RS Data.iff_trans;
in
  fun prove_rotate_ex_tac ctxt i = qcomm_tac ctxt excomm Data.iff_exI i
  fun prove_one_point_ex_tac ctxt =
    prove_rotate_ex_tac ctxt 1 THEN resolve_tac ctxt [Data.iffI] 1 THEN
    ALLGOALS
      (EVERY' [maybe_tac (eresolve_tac ctxt [Data.exE]),
        REPEAT_DETERM o eresolve_tac ctxt [Data.conjE],
        maybe_tac (resolve_tac ctxt [Data.exI]),
        DEPTH_SOLVE_1 o ares_tac ctxt [Data.conjI]])
end;

(* Proves (! x0..xn. (... & x0 = t & ...) --> P x0) =
          (! x1..xn x0. x0 = t --> (... & ...) --> P x0)
*)
local
  fun tac ctxt =
    SELECT_GOAL
      (EVERY1 [REPEAT o dresolve_tac ctxt [Data.uncurry],
        REPEAT o resolve_tac ctxt [Data.impI],
        eresolve_tac ctxt [Data.mp],
        REPEAT o eresolve_tac ctxt [Data.conjE],
        REPEAT o ares_tac ctxt [Data.conjI]]);
  val allcomm = Data.all_comm RS Data.iff_trans;
in
  fun prove_one_point_all_tac ctxt =
    EVERY1 [qcomm_tac ctxt allcomm Data.iff_allI,
      resolve_tac ctxt [Data.iff_allI],
      resolve_tac ctxt [Data.iffI], tac ctxt, tac ctxt];
end

(* Proves (! x0..xn. (... & x0 = t & ...) --> P x0) =
          (! x1..xn x0. x0 = t --> (... & ...) --> P x0)
*)
local
  val allcomm = Data.all_comm RS Data.iff_trans;
in
  fun prove_one_point_all_tac2 ctxt =
    EVERY1 [qcomm_tac ctxt allcomm Data.iff_allI,
      resolve_tac ctxt [Data.iff_allI],
      resolve_tac ctxt [Data.iffI], blast_tac ctxt, blast_tac ctxt];
end

fun renumber l u (Bound i) =
      Bound (if i < l orelse i > u then i else if i = u then l else i + 1)
  | renumber l u (s $ t) = renumber l u s $ renumber l u t
  | renumber l u (Abs (x, T, t)) = Abs (x, T, renumber (l + 1) (u + 1) t)
  | renumber _ _ atom = atom;

fun quantify qC x T xs P =
  let
    fun quant [] P = P
      | quant ((qC, x, T) :: xs) P = quant xs (qC $ Abs (x, T, P));
    val n = length xs;
    val Q = if n = 0 then P else renumber 0 n P;
  in if Data.rotate then quant xs (qC $ Abs (x, T, Q)) else qC $ Abs (x, T, quant xs P) end;

fun rearrange_all ctxt ct =
  (case Thm.term_of ct of
    F as (all as Const (q, _)) $ Abs (x, T, P) =>
      (case extract_quant extract_imp q P of
        NONE => NONE
      | SOME (xs, eq, Q) =>
          let val R = quantify all x T xs (Data.imp $ eq $ Q)
          in SOME (prove_conv ctxt (F, R) prove_one_point_all_tac) end)
  | _ => NONE);

fun rotate_all ctxt ct =
  let
    fun extract fst xs P =
      if fst then NONE else SOME (xs, P, P)
    in
  (case strip_prop (Thm.term_of ct) of
    F as (ex as Const (q, _)) $ Abs (x, T, P) =>
      (case extract_quant extract q P of
        NONE => NONE
      | SOME (xs, _, Q) =>
          let val R = quantify ex x T xs Q
          in SOME (prove_conv ctxt (F, R) prove_one_point_all_tac2) end)
  | _ => NONE) end;

fun rearrange_ball tac ctxt ct =
  (case Thm.term_of ct of
    F as Ball $ A $ Abs (x, T, P) =>
      (case extract_imp true [] P of
        NONE => NONE
      | SOME (xs, eq, Q) =>
          if not (null xs) then NONE
          else
            let val R = Data.imp $ eq $ Q
            in SOME (prove_conv ctxt (F, Ball $ A $ Abs (x, T, R)) tac) end)
  | _ => NONE);

fun rearrange_ex' ctxt trm =
  (case strip_prop trm of
    F as (ex as Const (q, _)) $ Abs (x, T, P) =>
      (case extract_quant (extract_conj []) q P of
        NONE => NONE
      | SOME (xs, eq, Q) =>
          let val R = quantify ex x T xs (Data.conj $ eq $ Q)
          in SOME (prove_conv ctxt (F, R) prove_one_point_ex_tac) end)
  | _ => NONE);

fun rearrange_ex ctxt = rearrange_ex' ctxt o Thm.term_of

fun rotate_ex ctxt ct =
  let
    fun extract fst xs P =
      if fst then NONE else SOME (xs, P, P)
    in
  (case strip_prop (Thm.term_of ct) of
    F as (ex as Const (q, _)) $ Abs (x, T, P) =>
      (case extract_quant extract q P of
        NONE => NONE
      | SOME (xs, _, Q) =>
          let val R = quantify ex x T xs Q
          in SOME (prove_conv ctxt (F, R) prove_one_point_ex_tac) end)
  | _ => NONE) end;

fun miniscope_ex ctxt ct =
  let
    fun extract fst xs t =
      case Data.dest_conj t of
        SOME (P, _) => if Data.move xs P [] andalso not fst then SOME (xs, t, t) else NONE
      | NONE => NONE
    in
  (case strip_prop (Thm.term_of ct) of
    F as (ex as Const (q, _)) $ Abs (x, T, P) =>
      (case extract_quant extract q P of
        NONE => NONE
      | SOME (xs, _, Q) =>
          let val R = quantify ex x T xs Q
          in SOME (prove_conv ctxt (F, R) prove_one_point_ex_tac) end)
  | _ => NONE) end;

fun rearrange_bex tac ctxt ct =
  (case Thm.term_of ct of
    F as Bex $ A $ Abs (x, T, P) =>
      (case extract_conj [] true [] P of
        NONE => NONE
      | SOME (xs, eq, Q) =>
          if not (null xs) then NONE
          else SOME (prove_conv ctxt (F, Bex $ A $ Abs (x, T, Data.conj $ eq $ Q)) tac))
  | _ => NONE);

fun rearrange_Collect tac ctxt ct =
  (case Thm.term_of ct of
    F as Collect $ Abs (x, T, P) =>
      (case extract_conj [] true [] P of
        NONE => NONE
      | SOME (_, eq, Q) =>
          let val R = Collect $ Abs (x, T, Data.conj $ eq $ Q)
          in SOME (prove_conv ctxt (F, R) tac) end)
  | _ => NONE);

end;

structure Quantifier1 = Quantifier
(
  (*abstract syntax*)
  fun dest_eq (Const(@{const_name HOL.eq},_) $ s $ t) = SOME (s, t)
    | dest_eq _ = NONE;
  fun dest_conj (Const(@{const_name HOL.conj},_) $ s $ t) = SOME (s, t)
    | dest_conj _ = NONE;
  fun dest_imp (Const(@{const_name HOL.implies},_) $ s $ t) = SOME (s, t)
    | dest_imp _ = NONE;
  val conj = HOLogic.conj
  val imp  = HOLogic.imp
  fun move xs eq _ =
  (case dest_eq eq of
    SOME (s, t) =>
      let val n = length xs in
        s = Bound n andalso not (loose_bvar1 (t, n)) orelse
        t = Bound n andalso not (loose_bvar1 (s, n))
      end
  | NONE => false);
  val force_move = true
  val rotate = true
  (*rules*)
  val iff_reflection = @{thm eq_reflection}
  val iffI = @{thm iffI}
  val iff_trans = @{thm trans}
  val conjI= @{thm conjI}
  val conjE= @{thm conjE}
  val impI = @{thm impI}
  val mp   = @{thm mp}
  val uncurry = @{thm uncurry}
  val exI  = @{thm exI}
  val exE  = @{thm exE}
  val iff_allI = @{thm iff_allI}
  val iff_exI = @{thm iff_exI}
  val all_comm = @{thm all_comm}
  val ex_comm = @{thm ex_comm}
);

(* loose_bvar2(t,k) iff t contains a 'loose' bound variable referring to
   a level below k. *)
fun loose_bvar2(Bound i,k) = i < k
  | loose_bvar2(f$t, k) = loose_bvar2(f,k) orelse loose_bvar2(t,k)
  | loose_bvar2(Abs(_,_,t),k) = loose_bvar2(t,k+1)
  | loose_bvar2 _ = false;

structure Quantifier2 = Quantifier
(
  (*abstract syntax*)
  fun dest_eq (Const(@{const_name HOL.eq},_) $ s $ t) = SOME (s, t)
    | dest_eq _ = NONE;
  fun dest_conj (Const(@{const_name HOL.conj},_) $ s $ t) = SOME (s, t)
    | dest_conj _ = NONE;
  fun dest_imp (Const(@{const_name HOL.implies},_) $ s $ t) = SOME (s, t)
    | dest_imp _ = NONE;
  val conj = HOLogic.conj
  val imp  = HOLogic.imp
  fun move xs t _ =  
      let val n = length xs in
        loose_bvar1 (t, n) andalso not (loose_bvar2 (t, n))
      end
  val force_move = false
  val rotate = false
  (*rules*)
  val iff_reflection = @{thm eq_reflection}
  val iffI = @{thm iffI}
  val iff_trans = @{thm trans}
  val conjI= @{thm conjI}
  val conjE= @{thm conjE}
  val impI = @{thm impI}
  val mp   = @{thm mp}
  val uncurry = @{thm uncurry}
  val exI  = @{thm exI}
  val exE  = @{thm exE}
  val iff_allI = @{thm iff_allI}
  val iff_exI = @{thm iff_exI}
  val all_comm = @{thm all_comm}
  val ex_comm = @{thm ex_comm}
);

structure Quantifier3 = Quantifier
(
  (*abstract syntax*)
  fun dest_eq (Const(@{const_name HOL.eq},_) $ s $ t) = SOME (s, t)
    | dest_eq _ = NONE;
  fun dest_conj (Const(@{const_name HOL.conj},_) $ s $ t) = SOME (s, t)
    | dest_conj _ = NONE;
  fun dest_imp (Const(@{const_name HOL.implies},_) $ s $ t) = SOME (s, t)
    | dest_imp _ = NONE;
  val conj = HOLogic.conj
  val imp  = HOLogic.imp
  fun move xs t _ =  
      let val n = length xs in
        loose_bvar1 (t, n) andalso not (loose_bvar (t, n + 1))
      end
  val force_move = false
  val rotate = false
  (*rules*)
  val iff_reflection = @{thm eq_reflection}
  val iffI = @{thm iffI}
  val iff_trans = @{thm trans}
  val conjI= @{thm conjI}
  val conjE= @{thm conjE}
  val impI = @{thm impI}
  val mp   = @{thm mp}
  val uncurry = @{thm uncurry}
  val exI  = @{thm exI}
  val exE  = @{thm exE}
  val iff_allI = @{thm iff_allI}
  val iff_exI = @{thm iff_exI}
  val all_comm = @{thm all_comm}
  val ex_comm = @{thm ex_comm}
);

signature Int_Param =
  sig
    val x : int
  end;

fun is_conj (Const(@{const_name HOL.conj},_) $ _ $ _) = true
    | is_conj _ = false;

functor Quantifier4 (to_move: Int_Param) = Quantifier
(
  (*abstract syntax*)
  fun dest_eq (Const(@{const_name HOL.eq},_) $ s $ t) = SOME (s, t)
    | dest_eq _ = NONE;
  fun dest_conj (Const(@{const_name HOL.conj},_) $ s $ t) = SOME (s, t)
    | dest_conj _ = NONE;
  fun dest_imp (Const(@{const_name HOL.implies},_) $ s $ t) = SOME (s, t)
    | dest_imp _ = NONE;
  val conj = HOLogic.conj
  val imp  = HOLogic.imp
  fun move _ P trms = length trms + 1 = to_move.x andalso not (is_conj P)
  val force_move = true
  val rotate = false
  (*rules*)
  val iff_reflection = @{thm eq_reflection}
  val iffI = @{thm iffI}
  val iff_trans = @{thm trans}
  val conjI= @{thm conjI}
  val conjE= @{thm conjE}
  val impI = @{thm impI}
  val mp   = @{thm mp}
  val uncurry = @{thm uncurry}
  val exI  = @{thm exI}
  val exE  = @{thm exE}
  val iff_allI = @{thm iff_allI}
  val iff_exI = @{thm iff_exI}
  val all_comm = @{thm all_comm}
  val ex_comm = @{thm ex_comm}
);

structure Quantifier5 = Quantifier
(
  (*abstract syntax*)
  fun dest_eq (Const(@{const_name HOL.eq},_) $ s $ t) = SOME (s, t)
    | dest_eq _ = NONE;
  fun dest_conj (Const(@{const_name HOL.conj},_) $ s $ t) = SOME (s, t)
    | dest_conj _ = NONE;
  fun dest_imp (Const(@{const_name HOL.implies},_) $ s $ t) = SOME (s, t)
    | dest_imp _ = NONE;
  val conj = HOLogic.conj
  val imp  = HOLogic.imp
  fun move _ t _ = is_conj t
  val force_move = true
  val rotate = false
  (*rules*)
  val iff_reflection = @{thm eq_reflection}
  val iffI = @{thm iffI}
  val iff_trans = @{thm trans}
  val conjI= @{thm conjI}
  val conjE= @{thm conjE}
  val impI = @{thm impI}
  val mp   = @{thm mp}
  val uncurry = @{thm uncurry}
  val exI  = @{thm exI}
  val exE  = @{thm exE}
  val iff_allI = @{thm iff_allI}
  val iff_exI = @{thm iff_exI}
  val all_comm = @{thm all_comm}
  val ex_comm = @{thm ex_comm}
);

structure Quantifier6 = Quantifier
(
  (*abstract syntax*)
  fun dest_eq (Const(@{const_name HOL.eq},_) $ s $ t) = SOME (s, t)
    | dest_eq _ = NONE;
  fun dest_conj (Const(@{const_name HOL.conj},_) $ s $ t) = SOME (s, t)
    | dest_conj _ = NONE;
  fun dest_imp (Const(@{const_name HOL.implies},_) $ s $ t) = SOME (s, t)
    | dest_imp _ = NONE;
  val conj = HOLogic.conj
  val imp  = HOLogic.imp
  fun move xs t _ =  
      let val n = length xs in
        not (loose_bvar1 (t, n))
      end
  val force_move = true
  val rotate = true
  (*rules*)
  val iff_reflection = @{thm eq_reflection}
  val iffI = @{thm iffI}
  val iff_trans = @{thm trans}
  val conjI= @{thm conjI}
  val conjE= @{thm conjE}
  val impI = @{thm impI}
  val mp   = @{thm mp}
  val uncurry = @{thm uncurry}
  val exI  = @{thm exI}
  val exE  = @{thm exE}
  val iff_allI = @{thm iff_allI}
  val iff_exI = @{thm iff_exI}
  val all_comm = @{thm all_comm}
  val ex_comm = @{thm ex_comm}
);

structure Quantifier7 = Quantifier
(
  (*abstract syntax*)
  fun dest_eq (Const(@{const_name HOL.eq},_) $ s $ t) = SOME (s, t)
    | dest_eq _ = NONE;
  fun dest_conj (Const(@{const_name HOL.conj},_) $ s $ t) = SOME (s, t)
    | dest_conj _ = NONE;
  fun dest_imp (Const(@{const_name HOL.implies},_) $ s $ t) = SOME (s, t)
    | dest_imp _ = NONE;
  val conj = HOLogic.conj
  val imp  = HOLogic.imp
  fun move xs t _ =  
      let val n = length xs in
        not (loose_bvar1 (t, n))
      end
  val force_move = true
  val rotate = true
  (*rules*)
  val iff_reflection = @{thm eq_reflection}
  val iffI = @{thm iffI}
  val iff_trans = @{thm trans}
  val conjI= @{thm conjI}
  val conjE= @{thm conjE}
  val impI = @{thm impI}
  val mp   = @{thm mp}
  val uncurry = @{thm uncurry}
  val exI  = @{thm exI}
  val exE  = @{thm exE}
  val iff_allI = @{thm iff_allI}
  val iff_exI = @{thm iff_exI}
  val all_comm = @{thm all_comm}
  val ex_comm = @{thm ex_comm}
);

\<close>

ML_val \<open>Quantifier1.rearrange_ex @{context} @{cterm "\<exists> a c. c < n \<and> a \<in> A"}\<close>
ML_val \<open>Quantifier1.rearrange_ex @{context} @{cterm "\<exists> a c. c < n \<and> a = b"}\<close>
ML_val \<open>Quantifier2.rearrange_ex @{context} @{cterm "\<exists> a c. a = b \<and> c < n"}\<close>
ML_val \<open>Quantifier1.rearrange_ex @{context} @{cterm "\<exists> a c. a = b \<and> c < n"}\<close>
ML_val \<open>Quantifier2.rearrange_ex @{context} @{cterm "\<exists> a c. c < n \<and> a = b"}\<close>
ML_val \<open>Quantifier2.rearrange_ex @{context} @{cterm "\<exists> a c. a < n \<and> a = b"}\<close>
ML_val \<open>Quantifier2.rearrange_ex @{context} @{cterm "\<exists> a c. a < n \<and> c < n \<and> a = b"}\<close>
ML_val \<open>Quantifier2.rearrange_ex @{context} @{cterm "\<exists> a c. c < n \<and> a > c"}\<close>
ML_val \<open>Quantifier3.rearrange_ex @{context} @{cterm "\<exists> a c. c < n \<and> a > c"}\<close>
ML_val \<open>Quantifier2.rearrange_ex @{context} @{cterm "\<exists> a c. c < n \<and> a > b"}\<close>
ML_val \<open>Quantifier2.rearrange_ex @{context} @{cterm "\<exists> a c. c < n \<and> (P a c \<and> a > b) \<and> Q c"}\<close>
ML_val \<open>Quantifier2.rearrange_ex @{context} @{cterm "finite {(a, c) | a c. c < n \<and> a \<in> A}"}\<close>
ML_val \<open>Quantifier2.rearrange_ex @{context} @{cterm "finite {t. \<exists> a c. a \<in> A \<and> c < n \<and> t = (a,c)}"}\<close>
ML_val \<open>Quantifier1.rotate_ex @{context} @{cterm "\<exists> a c. c < n \<and> a > b"}\<close>
ML_val \<open>Quantifier1.rotate_ex @{context} @{cterm "\<exists> a c d. c < n \<and> a > b \<and> P d"}\<close>
ML_val \<open>Quantifier1.rearrange_ex @{context} @{cterm "\<exists> a c. a < n \<and> c = b"}\<close>
ML_val \<open>Quantifier1.rearrange_ex @{context} @{cterm "\<forall> a. \<exists> c. a < n \<and> c = b"}\<close>
ML_val \<open>Quantifier1.rearrange_ex @{context} @{cterm "\<forall> a c. a < n \<and> c = b"}\<close>
ML_val \<open>Quantifier6.rearrange_ex @{context} @{cterm "\<exists> a b c. a < n \<and> b < 3 \<and> b > c"}\<close>
ML_val \<open>Quantifier6.rearrange_ex @{context} @{cterm "\<exists>b c. a < n \<and> b < 3 \<and> b > c"}\<close>
ML_val \<open>Quantifier7.miniscope_ex @{context} @{cterm "\<exists> a b c. a < n \<and> b < 3 \<and> b > c"}\<close>
ML_val \<open>Quantifier7.miniscope_ex @{context} @{cterm "\<exists>b c. a < n \<and> b < 3 \<and> b > c"}\<close>

simproc_setup ex_reorder ("\<exists>x. P x") = \<open>fn _ => Quantifier2.rearrange_ex\<close>
declare [[simproc del: ex_reorder]]
simproc_setup ex_reorder2 ("\<exists>x. P x") = \<open>fn _ => Quantifier3.rearrange_ex\<close>
declare [[simproc del: ex_reorder2]]
simproc_setup ex_reorder3 ("\<exists>x. P x") = \<open>fn _ => Quantifier6.rearrange_ex\<close>
declare [[simproc del: ex_reorder3]]
simproc_setup ex_reorder4 ("\<exists>x. P x") = \<open>fn _ => Quantifier7.miniscope_ex\<close>
declare [[simproc del: ex_reorder4]]

ML_val \<open>@{term "\<exists> a c. c < n \<and> a \<in> A"}\<close>

ML_val \<open>@{term "finite {(a, c). c < n \<and> a \<in> A}"}\<close>

ML_val \<open>@{term "finite {(a, c) | a c. c < n \<and> a \<in> A}"}\<close>

lemma
  fixes n :: nat
  assumes A: "finite A"
  shows "finite {(a, c). c < n \<and> a \<in> A}"
  using assms
    using [[simproc add: finite_Collect]]
    by simp

lemma
  fixes n :: nat
  assumes A: "finite A"
  shows "finite {(a, c) | a c. c < n \<and> a \<in> A}"
  using assms
  using [[simproc add: ex_reorder]]
    by simp

lemma
  fixes n :: nat
  assumes A: "finite A"
  shows "finite {t. \<exists> a c. a \<in> A \<and> c < n \<and> t = (a,c)}"
  apply simp
  using assms apply simp
  oops

lemma
  fixes n :: nat
  assumes A: "finite A"
  shows "finite {t. \<exists> a c. (t = (a,c) \<and> c < n) \<and> a \<in> A}"
      using [[simproc add: ex_reorder]]
  using [[simp_trace]] apply simp
  using assms by simp

lemma
  fixes n :: nat
  assumes A: "finite A"
  shows "finite {t. \<exists> a c. (t = (a,c) \<and> a \<in> A) \<and> c < n}"
  using [[simp_trace]] apply (simp del: Product_Type.Collect_case_prod)
  using assms by simp
  
lemma
  fixes n :: nat
  assumes A: "finite A"
  shows "finite {t. \<exists> a c. (a \<in> A \<and> t = (a,c)) \<and> c < n}"
  using [[simp_trace]] apply simp
  using assms by simp
  
lemma
  fixes n :: nat
  assumes A: "finite A"
  shows "finite {t. \<exists> a c. a \<in> A \<and> c < n \<and> t = (a,c)}"
  using [[simp_trace]] apply simp
  using assms by simp
  
lemma
  assumes A: "finite A"
  shows "finite {t. \<exists> a c. a \<in> A \<and> P c \<and> t = (a,c)}"
  using [[simp_trace]] apply simp
  using assms apply simp
  oops

ML \<open>
  fun rotate_quant reorder_thm n ctxt =
    let
      fun subst j =
        if j > n then K all_tac else
          (
            EqSubst.eqsubst_tac ctxt [j] [reorder_thm]
          ) THEN' subst (j + 1)
    in subst 1 end;
\<close>

ML_val Pretty.string_of
ML_val Syntax.pretty_term

ML \<open>
  fun rotate_ex_tac ctxt =
    let
      fun foc_tac {concl, ...} =
        case Quantifier1.rotate_ex ctxt concl of
          NONE => no_tac
        | SOME thm => rewrite_goals_tac ctxt [thm]
    in
      Subgoal.FOCUS foc_tac ctxt
    end;
\<close>

ML \<open>
  fun rotate_all_tac ctxt =
    let
      fun foc_tac {concl, ...} =
        case Quantifier1.rotate_all ctxt concl of
          NONE => no_tac
        | SOME thm => rewrite_goals_tac ctxt [thm]
    in
      Subgoal.FOCUS foc_tac ctxt
    end;
\<close>

ML \<open>
  fun rearrange_ex_tac ctxt =
    let
      fun foc_tac {concl, ...} =
        case Quantifier2.rearrange_ex ctxt concl of
          NONE => no_tac
        | SOME thm => rewrite_goals_tac ctxt [thm]
    in
      Subgoal.FOCUS foc_tac ctxt
    end;
\<close>

ML \<open>
  fun rearrange_ex_tac2 ctxt =
    let
      fun foc_tac {concl, ...} =
        case Quantifier3.rearrange_ex ctxt concl of
          NONE => no_tac
        | SOME thm => rewrite_goals_tac ctxt [thm]
    in
      Subgoal.FOCUS foc_tac ctxt
    end;
\<close>

(* XXX How to do this? *)
(*
ML \<open>
  fun rearrange_ex_tac2 n ctxt =
    let
      struct Quant = Quantifier4(val x = n);
      fun foc_tac {concl, ...} =
        case Quantifier4.rearrange_ex ctxt concl of
          NONE => no_tac
        | SOME thm => rewrite_goals_tac ctxt [thm]
    in
      Subgoal.FOCUS foc_tac ctxt
    end;
\<close>
*)

ML_val Abs

ML_val Conv.rewr_conv ML_val Thm.dest_abs

ML \<open>

  fun strip_fin (Const (@{const_name "finite"}, _) $ (Const (@{const_name "Collect"}, _) $ t)) = t
    | strip_fin t = t

  fun wrap_fin tac ctxt = tac ctxt o strip_fin

  structure Quant2 = Quantifier4(val x = 2);
  structure Quant3 = Quantifier4(val x = 3);
  structure Quant4 = Quantifier4(val x = 4);
  structure Quant5 = Quantifier4(val x = 5);

  fun rearrange_ex_fixed_n rearrange_n ctxt =
    let
      fun foc_tac {concl, ...} =
        case rearrange_n ctxt concl of
          NONE => no_tac
        | SOME thm => rewrite_goals_tac ctxt [thm, @{thm HOL.conj_assoc} RS @{thm HOL.eq_reflection}]
    in
      Subgoal.FOCUS foc_tac ctxt
    end;
  
  val rearrange_ex_fixed_2 = rearrange_ex_fixed_n Quant2.rearrange_ex;
  val rearrange_ex_fixed_3 = rearrange_ex_fixed_n Quant3.rearrange_ex;
  val rearrange_ex_fixed_4 = rearrange_ex_fixed_n Quant4.rearrange_ex;
  val rearrange_ex_fixed_5 = rearrange_ex_fixed_n Quant5.rearrange_ex;

  (* val defer_ex = rearrange_ex_fixed_n (wrap_fin Quantifier5.rearrange_ex); *)

  fun CONV conv ctxt =
    let
      fun foc_tac {concl, ...} =
        rewrite_goals_tac ctxt [conv ctxt concl]
    in
      Subgoal.FOCUS foc_tac ctxt
    end;

  fun mk_conv f ctxt ct =
    case (f ctxt ct) of
      SOME thm => thm
    | _ => raise CTERM ("no conversion", [])

  fun success_conv cv ct =
    let
      val eq = cv ct
    in
      if Thm.is_reflexive eq then raise CTERM ("no conversion", []) else eq
    end

  fun mk_conv' f ctxt ct = the_default (Thm.reflexive ct) (f ctxt ct)
  val assoc_conv = Conv.rewr_conv (@{thm HOL.conj_assoc} RS @{thm HOL.eq_reflection})
  val comm_conv = Conv.rewr_conv (@{thm HOL.conj_commute} RS @{thm HOL.eq_reflection})
  fun wrap_conv f ctxt =
    success_conv (
      Conv.top_sweep_conv (fn ctxt => mk_conv f ctxt then_conv Conv.repeat_conv assoc_conv) ctxt
    )
  fun mk_tac conv ctxt = CONVERSION (Conv.concl_conv ~1 (Object_Logic.judgment_conv ctxt (conv ctxt)))

  val defer_conv = mk_conv Quantifier5.rearrange_ex
  val conv = wrap_conv Quantifier5.rearrange_ex
  fun defer_ex_tac ctxt = CONVERSION (Conv.params_conv ~1 (fn ctxt => Conv.concl_conv ~1 (conv ctxt)) ctxt)
  val defer_ex_tac = CONV conv
  fun defer_ex_tac ctxt i =
    CHANGED (mk_tac (fn ctxt => wrap_conv Quantifier5.rearrange_ex ctxt else_conv Conv.top_sweep_conv (K comm_conv) ctxt) ctxt i)
  val mini_ex_tac = mk_tac (wrap_conv Quantifier6.rearrange_ex)
  val mini_ex_tac2 = mk_tac (wrap_conv Quantifier7.miniscope_ex)

  val rearrange_ex_fixed_2 = mk_tac (wrap_conv Quant2.rearrange_ex);
  val rearrange_ex_fixed_3 = mk_tac (wrap_conv Quant3.rearrange_ex);
  val rearrange_ex_fixed_4 = mk_tac (wrap_conv Quant4.rearrange_ex);
  val rearrange_ex_fixed_5 = mk_tac (wrap_conv Quant5.rearrange_ex);
\<close>

ML_val Object_Logic.judgment_conv

ML_val \<open>defer_conv @{context} @{cterm "\<exists> a b c d. a < 1 \<and> b < 2 \<and> c < 3 \<and> d < 4"}\<close>
ML_val \<open>assoc_conv @{cterm "(a < 1 \<and> b < 2) \<and> c < 3 \<and> d < 4"}\<close>
ML_val \<open>Conv.binder_conv (K assoc_conv) @{context} @{cterm "\<exists> a. (a < 1 \<and> b < 2) \<and> c < 3 \<and> d < 4"}\<close>
ML_val \<open>Conv.top_sweep_conv (K assoc_conv) @{context} @{cterm "\<exists> a b c d. (a < 1 \<and> b < 2) \<and> c < 3 \<and> d < 4"}\<close>
ML_val \<open>Conv.bottom_conv (K (Conv.try_conv assoc_conv)) @{context} @{cterm "\<exists> a b c d. (a < 1 \<and> b < 2) \<and> c < 3 \<and> d < 4"}\<close>
ML_val \<open>Conv.every_conv [defer_conv @{context}, Conv.try_conv assoc_conv] @{cterm "\<exists> a b c d. a < 1 \<and> b < 2 \<and> c < 3 \<and> d < 4"}\<close>
ML_val \<open>conv @{context} @{cterm "\<exists> a b c d. a < 1 \<and> b < 2 \<and> c < 3 \<and> d < 4"}\<close>
ML_val \<open>conv @{context} @{cterm "finite {t. \<exists> a b c d. a < 1 \<and> b < 2 \<and> c < 3 \<and> d < 4}"}\<close>
ML_val \<open>conv @{context} @{cterm "\<exists>a b c d. d = 4 \<and> c = 3 \<and> b < 2 \<and> a < 1"}\<close>

ML_val \<open>CONVERSION (Conv.concl_conv ~1 (conv @{context}))\<close>
ML_val Conv.concl_conv

ML_val \<open>Quantifier1.rotate_ex @{context} @{cterm "\<exists> a b c d. a < 1 \<and> b < 2 \<and> c < 3 \<and> d < 4"}\<close>

ML_val \<open>Quantifier1.rotate_all @{context} @{cterm "\<forall> a b c d. a < 1 \<and> b < 2 \<and> c < 3 \<and> d < 4"}\<close>

lemma
  "\<forall> a b c d. a < 1 \<and> b < 2 \<and> c < 3 \<and> d < 4"
  apply (tactic \<open>rotate_all_tac @{context} 1\<close>)
  apply (tactic \<open>rotate_all_tac @{context} 1\<close>)
  apply (tactic \<open>rotate_all_tac @{context} 1\<close>)
  apply (tactic \<open>rotate_all_tac @{context} 1\<close>)
  apply (tactic \<open>rotate_all_tac @{context} 1\<close>)
  oops

lemmas a = HOL.refl[THEN eq_reflection]
lemmas b = enum_the_def[THEN eq_reflection]
ML_val \<open>Thm.is_reflexive @{thm a}\<close>
ML_val \<open>Thm.is_reflexive @{thm b}\<close>
lemma
  "\<exists> a b c d. a < 1 \<and> b < 2 \<and> c = 3 \<and> d = 4"
  apply (tactic \<open>rearrange_ex_fixed_2 @{context} 1\<close>)
  apply (tactic \<open>rearrange_ex_fixed_3 @{context} 1\<close>)
  apply (tactic \<open>rearrange_ex_fixed_4 @{context} 1\<close>)
  apply (tactic \<open>defer_ex_tac @{context} 1\<close>)
  apply (subst conj_assoc)+
  oops

  ML_val \<open>@{const_name finite}\<close>
  ML_val \<open>@{const_name Collect}\<close>
ML_val \<open>strip_fin @{term \<open>finite {t. \<exists>a b c d. a < 1 \<and> b < 2 \<and> c = 3 \<and> d = 4}\<close>}\<close>


lemma
  "finite {t. \<exists> a b c d. a < 1 \<and> b < 2 \<and> c = 3 \<and> d = 4}"
  apply (tactic \<open>rearrange_ex_fixed_2 @{context} 1\<close>)
  apply (tactic \<open>rearrange_ex_fixed_3 @{context} 1\<close>)
  apply (tactic \<open>rearrange_ex_fixed_4 @{context} 1\<close>)
  apply (tactic \<open>defer_ex_tac @{context} 1\<close>)
  oops
  
lemma
  "finite S \<Longrightarrow> finite {t. \<exists> a b c d. a < 1 \<and> b < 2 \<and> c = 3 \<and> d = 4}"
  apply (tactic \<open>rearrange_ex_fixed_2 @{context} 1\<close>)
  apply (tactic \<open>rearrange_ex_fixed_3 @{context} 1\<close>)
  apply (tactic \<open>rearrange_ex_fixed_4 @{context} 1\<close>)
  apply (tactic \<open>defer_ex_tac @{context} 1\<close>, simp only: conj_assoc)
  oops

lemma
  "finite S \<Longrightarrow> finite {t. \<exists> a b c d. P a b d \<and> c > 3}"
  apply (tactic \<open>defer_ex_tac @{context} 1\<close>)
  apply (tactic \<open>mini_ex_tac @{context} 1\<close>)
  apply (simp only: ex_simps)
  oops

lemma
  "\<exists> a b c d. d < 4 \<and> a < 1 \<and> b < 2 \<and> c < 3 \<and> d < 4"
  using [[simproc add: ex_reorder3]]
  apply simp
  oops

lemma
  "\<exists> a b c d. d < 4 \<and> a < 1 \<and> b < 2 \<and> c < 3 \<and> d < 4"
  using [[simproc add: ex_reorder4]]
  apply simp
  oops

lemma
  "\<exists> a b c d. d < 4 \<and> a < 1 \<and> b < 2 \<and> c < 3 \<and> d < 4"
  apply (tactic \<open>mini_ex_tac @{context} 1\<close>)
  apply simp
  apply (tactic \<open>mini_ex_tac @{context} 1\<close>)
  apply simp
  apply (tactic \<open>mini_ex_tac @{context} 1\<close>)
  apply simp
  apply (tactic \<open>mini_ex_tac @{context} 1\<close>)
  apply simp
  apply (tactic \<open>mini_ex_tac @{context} 1\<close>)
  apply simp
  apply (tactic \<open>mini_ex_tac @{context} 1\<close>)
  apply simp
  oops

lemma
  "\<exists> a b c d. d < 4 \<and> a < 1 \<and> b < 2 \<and> c < 3 \<and> d < 4"
  apply (tactic \<open>mini_ex_tac2 @{context} 1\<close>)
  apply simp
  apply (tactic \<open>mini_ex_tac2 @{context} 1\<close>)
  apply simp
  apply (tactic \<open>mini_ex_tac2 @{context} 1\<close>)
  apply simp
  apply (tactic \<open>mini_ex_tac @{context} 1\<close>)
  apply simp
  apply (tactic \<open>mini_ex_tac @{context} 1\<close>)
  apply simp
  apply (tactic \<open>mini_ex_tac @{context} 1\<close>)
  apply simp
  oops
  
lemma
  "\<exists> a c b d. d < 4 \<and> a < 1 \<and> b < 2 \<and> c < 3"
  apply simp
  oops
  
lemma
  "\<exists> a b c d. a < 1 \<and> b < 2 \<and> c < 3 \<and> d < 4"
  apply (tactic \<open>rotate_ex_tac @{context} 1\<close>)
  apply (tactic \<open>rotate_ex_tac @{context} 1\<close>)
  apply (tactic \<open>rotate_ex_tac @{context} 1\<close>)
  apply (tactic \<open>rotate_ex_tac @{context} 1\<close>)
  apply (tactic \<open>rotate_ex_tac @{context} 1\<close>)
  oops

lemma
  "\<exists> a b c d. b < 2 \<and> c < 3 \<and> d < 4 \<and> a < 1"
  apply (tactic \<open>rearrange_ex_tac @{context} 1\<close>)
  oops

lemma
  "\<exists> a b c d. b < 2 \<and> c < 3 \<and> d < 4 \<and> a < c"
  apply (tactic \<open>rearrange_ex_tac2 @{context} 1\<close>; simp only: conj_assoc)+
  oops

lemma
  "\<exists> a b c d. b < 2 \<and> c < 3 \<and> d < 4 \<and> a < c"
  apply (tactic \<open>rearrange_ex_tac2 @{context} 1\<close>; simp del: ex_simps)+
  oops

lemma
  "\<exists> a b c d. b < 2 \<and> c < 3 \<and> d < 4 \<and> a < c"
  apply (tactic \<open>rearrange_ex_tac2 @{context} 1\<close>)
  apply (simp del: ex_simps)
  apply (tactic \<open>rearrange_ex_tac2 @{context} 1\<close>)
  apply (simp del: ex_simps)
  apply (tactic \<open>rearrange_ex_tac2 @{context} 1\<close>)
  using [[simp_trace]]
  apply (simp del: ex_simps)
  oops

lemma finite_Collect_bounded_ex_4:
  assumes "finite {(a,b,c,d) . P a b c d}"
  shows
    "finite {x. \<exists>a b c d. P a b c d \<and> Q x a b c d}
    \<longleftrightarrow> (\<forall> a b c d. P a b c d \<longrightarrow> finite {x. Q x a b c d})"
proof -
  have *:
    "{x. \<exists>a b c d. P a b c d \<and> Q x a b c d}
    = {x. \<exists> t. t \<in> {(a,b,c,d). P a b c d} \<and> (\<exists>a b c d. t = (a, b, c, d) \<and> Q x a b c d)}"
    by simp
  show ?thesis apply (subst *)
    apply (subst finite_Collect_bounded_ex)
    using assms by simp+
oops
  
lemma finite_Collect_bounded_ex_4':
  assumes "finite {(a,b,c,d) | a b c d. P a b c d}"
  shows
    "finite {x. \<exists>a b c d. P a b c d \<and> Q x a b c d}
    \<longleftrightarrow> (\<forall> a b c d. P a b c d \<longrightarrow> finite {x. Q x a b c d})"
proof -
  have *:
    "{x. \<exists>a b c d. P a b c d \<and> Q x a b c d}
    = {x. \<exists> t. t \<in> {(a,b,c,d) | a b c d. P a b c d} \<and> (\<exists>a b c d. t = (a, b, c, d) \<and> Q x a b c d)}"
    by simp
  show ?thesis apply (subst *)
    apply (subst finite_Collect_bounded_ex)
    using assms by simp+
qed

lemma finite_Collect_bounded_ex_2 [simp]:
  assumes "finite {(a,b). P a b}"
  shows
    "finite {x. \<exists>a b. P a b \<and> Q x a b}
    \<longleftrightarrow> (\<forall> a b. P a b \<longrightarrow> finite {x. Q x a b})"
  using assms finite_Collect_bounded_ex[OF assms, where Q = "\<lambda> x. \<lambda> (a, b). Q x a b"]
  by clarsimp (* force, simp *)

lemma finite_Collect_bounded_ex_3 [simp]:
  assumes "finite {(a,b,c) . P a b c}"
  shows
    "finite {x. \<exists>a b c. P a b c \<and> Q x a b c}
    \<longleftrightarrow> (\<forall> a b c. P a b c \<longrightarrow> finite {x. Q x a b c})"
  using assms finite_Collect_bounded_ex
    [OF assms, where Q = "\<lambda> x. \<lambda> (a, b, c). Q x a b c"]
  by clarsimp

lemma finite_Collect_bounded_ex_4 [simp]:
  assumes "finite {(a,b,c,d) . P a b c d}"
  shows
    "finite {x. \<exists>a b c d. P a b c d \<and> Q x a b c d}
    \<longleftrightarrow> (\<forall> a b c d. P a b c d \<longrightarrow> finite {x. Q x a b c d})"
  using assms finite_Collect_bounded_ex[OF assms, where Q = "\<lambda> x. \<lambda> (a, b, c, d). Q x a b c d"]
  by clarsimp (* force, simp *)

lemma finite_Collect_bounded_ex_5 [simp]:
  assumes "finite {(a,b,c,d,e) . P a b c d e}"
  shows
    "finite {x. \<exists>a b c d e. P a b c d e \<and> Q x a b c d e}
    \<longleftrightarrow> (\<forall> a b c d e. P a b c d e \<longrightarrow> finite {x. Q x a b c d e})"
  using assms finite_Collect_bounded_ex
    [OF assms, where Q = "\<lambda> x. \<lambda> (a, b, c, d, e). Q x a b c d e"]
  by clarsimp (* force, simp *)

lemma finite_Collect_bounded_ex_6 [simp]:
  assumes "finite {(a,b,c,d,e,f) . P a b c d e f}"
  shows
    "finite {x. \<exists>a b c d e f. P a b c d e f \<and> Q x a b c d e f}
    \<longleftrightarrow> (\<forall> a b c d e f. P a b c d e f \<longrightarrow> finite {x. Q x a b c d e f})"
  using assms finite_Collect_bounded_ex
    [OF assms, where Q = "\<lambda> x. \<lambda> (a, b, c, d, e, f). Q x a b c d e f"]
  by clarsimp (* force, simp *)

lemma finite_Collect_bounded_ex_7 [simp]:
  assumes "finite {(a,b,c,d,e,f,g) . P a b c d e f g}"
  shows
    "finite {x. \<exists>a b c d e f g. P a b c d e f g \<and> Q x a b c d e f g}
    \<longleftrightarrow> (\<forall> a b c d e f g. P a b c d e f g \<longrightarrow> finite {x. Q x a b c d e f g})"
  using assms finite_Collect_bounded_ex
    [OF assms, where Q = "\<lambda> x. \<lambda> (a, b, c, d, e, f, g). Q x a b c d e f g"]
  by clarsimp (* force, simp *)

lemma finite_Collect_bounded_ex_8 [simp]:
  assumes "finite {(a,b,c,d,e,f,g,h) . P a b c d e f g h}"
  shows
    "finite {x. \<exists>a b c d e f g h. P a b c d e f g h \<and> Q x a b c d e f g h}
    \<longleftrightarrow> (\<forall> a b c d e f g h. P a b c d e f g h \<longrightarrow> finite {x. Q x a b c d e f g h})"
  using assms finite_Collect_bounded_ex
    [OF assms, where Q = "\<lambda> x. \<lambda> (a, b, c, d, e, f, g, h). Q x a b c d e f g h"]
  by clarsimp (* force, simp *)

lemma finite_Collect_bounded_ex_9 [simp]:
  assumes "finite {(a,b,c,d,e,f,g,h,i) . P a b c d e f g h i}"
  shows
    "finite {x. \<exists>a b c d e f g h i. P a b c d e f g h i \<and> Q x a b c d e f g h i}
    \<longleftrightarrow> (\<forall> a b c d e f g h i. P a b c d e f g h i \<longrightarrow> finite {x. Q x a b c d e f g h i})"
  using assms finite_Collect_bounded_ex
    [OF assms, where Q = "\<lambda> x. \<lambda> (a, b, c, d, e, f, g, h, i). Q x a b c d e f g h i"]
  by clarsimp (* force, simp *)

lemma finite_Collect_bounded_ex_10 [simp]:
  assumes "finite {(a,b,c,d,e,f,g,h,i,j) . P a b c d e f g h i j}"
  shows
    "finite {x. \<exists>a b c d e f g h i j. P a b c d e f g h i j \<and> Q x a b c d e f g h i j}
    \<longleftrightarrow> (\<forall> a b c d e f g h i j. P a b c d e f g h i j \<longrightarrow> finite {x. Q x a b c d e f g h i j})"
  using assms finite_Collect_bounded_ex
    [OF assms, where Q = "\<lambda> x. \<lambda> (a, b, c, d, e, f, g, h, i, j). Q x a b c d e f g h i j"]
  by clarsimp (* force, simp *)

end
