theory JANI
  imports Simple_Networks.Simple_Network_Language
begin

notation (input) TAG ("_ \<bbar> _" [40, 40] 41)

section \<open>Simple networks of automata with synchronization vectors and committed locations\<close>

text \<open>This is a generalization of the previous formalism with synchronization vectors in the style
of \<^emph>\<open>TChecker\<close>, see \<^url>\<open>https://github.com/fredher/tchecker/blob/master/doc/file-format.md\<close>.\<close>

text \<open>A single synchronization vector has the form \<open>sync:P1@a:P2@b:P3@c?:P4@d?\<close>
in TChecker's syntax, specifying that \<open>P1\<close> and \<open>P2\<close> \<^emph>\<open>need\<close> to synchronize on \<open>a\<close> and \<open>b\<close>,
respectively, while \<open>P3\<close> and \<open>P4\<close> \<^emph>\<open>will\<close> synchronize on \<open>c\<close> and \<open>d\<close> if they can
(\<^emph>\<open>weak\<close> synchronization constraint).
The order of processes in the synchronization specifies the order of updates.
Therefore we end up with the following type definition:\<close>

type_synonym identifier = string

type_synonym lvalue = identifier

record element =
  automaton :: string
  input_enable :: "identifier list" \<comment> \<open>Kill option for convenience\<close>
  comment :: "string option"

record sync =
  synchronise :: "identifier option list"
  result :: "identifier option" \<comment> \<open>NB: we label transitions with \<open>sync\<close> not just \<open>result\<close>\<close>
  comment :: "string option"

record composition =
  elements :: "element list"
  syncs :: "sync list" \<comment> \<open>Kill option for convenience\<close>
  comment :: "string option"

text \<open>Conversion procedure:
\<^item> Map \<open>field?: typ\<close> to \<open>field :: typ option\<close>
\<^item> Map \<open>typ | null\<close> to \<open>typ option\<close>
\<^item> Map \<open>Array.of schema\<close> to \<open><schema> list\<close>
\<^item> \<open><\<dots>>\<close> denotes recursive application of the procedure
\<^item> Give names to anonymous schemas
\<^item> Use SML-style type names
\<^item> Convert \<open>-\<close> to \<open>_\<close> in field names
\<close>

record bounded_type =
  lower_bound :: int
  upper_bound :: int

datatype type = TBounded bounded_type | TClock

type_synonym expression = "(identifier, int) exp"
type_synonym condition  = "(identifier, int) bexp"

record variable_declaration =
  name :: identifier
  type :: type
  transient :: "bool" \<comment> \<open>Kill option for convenience\<close>
  initial_value :: "expression option"

\<^cancel>\<open>type_synonym constant_declaration = \<dots>\<close>

record action =
  name :: identifier
  comment :: "string option"

record transient_value =
  ref :: lvalue \<comment> \<open>what to set the value for\<close>
  "value" :: expression \<comment> \<open>the value, must not contain references to transient variables or variables of type\<close>
                        \<comment> \<open>"clock" or "continuous"\<close>
  comment :: "string option" \<comment> \<open>an optional comment\<close>

record location =
  name :: identifier \<comment> \<open>the name of the location, unique among all locations of this automaton\<close>
  time_progress :: \<comment> \<open>the location's time progress condition, not allowed except TA, PTA, STA, HA, PHA and STA,\<close>
                        \<comment> \<open>type bool; if omitted in TA, PTA, STA, HA, PHA or SHA, it is true\<close>
    "condition option"
  transient_values :: "transient_value list" \<comment> \<open>values for transient variables in this location\<close>
    \<comment> \<open>XXX: ignored in semantics\<close>

record assignment =
  ref :: lvalue
  "value" :: expression
  "index" :: nat \<comment> \<open>Kill option for convenience\<close>
  "comment" :: "string option"

record destination =
  location :: identifier
  probability :: "unit option"
  assignments :: "assignment list" \<comment> \<open>Kill option for convenience\<close>
  "comment" :: "string option"

record edge =
  location :: identifier
  action :: "identifier option"
  rate :: "unit option"
  guard :: "condition" \<comment> \<open>Kill option for convenience\<close>
  destinations :: "destination list"
  "comment" :: "string option"

record automaton =
  name :: identifier
  variables :: "variable_declaration list" \<comment> \<open>Kill option for convenience\<close>
  restrict_initial :: "unit option"
  locations :: "location list"
  initial_locations :: "identifier list"
  edges :: "edge list"
  "comment" :: "string option"

record model =
  jani_version :: int
  name :: string
  metadata :: unit
  type :: unit
  features :: "unit option"
  actions :: "action list" \<comment> \<open>Kill option for convenience\<close>
  constants :: "unit list" \<comment> \<open>Kill option for convenience\<close>
  variables :: "variable_declaration list" \<comment> \<open>Kill option for convenience\<close>
  restrict_initial :: "unit option"
  properties :: "unit" \<comment> \<open>Kill option for convenience\<close>
  automata :: "automaton list"
  system :: composition

datatype label = Del | Internal | Sync sync

no_notation step_sn ("_ \<turnstile> \<langle>_, _, _\<rangle> \<rightarrow>\<^bsub>_\<^esub> \<langle>_, _, _\<rangle>" [61,61,61,61,61] 61)
no_notation steps_sn ("_ \<turnstile> \<langle>_, _, _\<rangle> \<rightarrow>* \<langle>_, _, _\<rangle>" [61, 61, 61,61,61] 61)
no_notation Simple_Network_Language.step_u ("_ \<turnstile> \<langle>_, _, _\<rangle> \<rightarrow>\<^bsub>_\<^esub> \<langle>_, _, _\<rangle>" [61,61,61,61,61] 61)

type_synonym dstate = "identifier \<rightharpoonup> int"
type_synonym cstate = "(identifier, real) cval"

inductive is_bval :: "dstate \<Rightarrow> cstate \<Rightarrow> condition \<Rightarrow> bool \<Rightarrow> bool" and is_eval
  where
  "is_bval s u true True" |
  "is_bval s u (not e) (\<not> b)" if "is_bval s u e b" |
  "is_bval s u (and e1 e2) (a \<and> b)" if "is_bval s u e1 a" "is_bval s u e2 b" |
  "is_bval s u (or e1 e2) (a \<or> b)" if "is_bval s u e1 a" "is_bval s u e2 b" |
  "is_bval s u (imply e1 e2) (a \<longrightarrow> b)" if "is_bval s u e1 a" "is_bval s u e2 b" |
  "is_bval s u (eq a b) (x = v)" if "is_eval s u a v" "is_eval s u b x" |
  "is_bval s u (le a b) (v \<le> x)" if "is_eval s u a v" "is_eval s u b x" |
  "is_bval s u (lt a b) (v < x)" if "is_eval s u a v" "is_eval s u b x" |
  "is_bval s u (ge a b) (v \<ge> x)" if "is_eval s u a v" "is_eval s u b x" |
  "is_bval s u (gt a b) (v > x)" if "is_eval s u a v" "is_eval s u b x" |
  "is_eval s u (const c) (real_of_int c)" |
  "is_eval s u (var x)   (real_of_int v)" if "s x = Some v" |
  "is_eval s u (var c)   v" if "u c = v" |
  "is_eval s u (if_then_else b e1 e2) (if bv then v1 else v2)"
  if "is_eval s u e1 v1" "is_eval s u e2 v2" "is_bval s u b bv" |
  "is_eval s u (binop f e1 e2) (f v1 v2)" if "is_eval s u e1 v1" "is_eval s u e2 v2" |
  "is_eval s u (unop f e) (f v)" if "is_eval s u e v"

text \<open>Some sanity assumptions that should be added to the locale:
\<^item> Clock variables and discrete variables need to be distinct
\<^item> Clock updates have a specific shape
\<^item> Destinations are only singleton
\<^item> All used variables are declared (so far globally)
\<^item> Every variable is only declared once
\<^item> Time progress conditions should only constrain clock variables
\<^item> All automata in the system are declared in the model
  (could check the converse to avoid modeling errors)
\<^item> Synchronizations without strong constraints
\<^item> No transient values on invariants
\<^item> Transient variables need to be initialized with a constant expression
\<close>

locale JANI =
  fixes model :: model
begin

definition N where
  "N i \<equiv>
  let
    name = automaton (elements (system model) ! i)
  in
    the (find (\<lambda>a. automaton.name a = name) (automata model))"

\<^cancel>\<open>definition guard_of_bexp where
  "guard_of_bexp s b = the (dest_conj (bsimp s b))"
\<close>
\<^cancel>\<open>definition inv where
  "inv i l \<equiv> the_default true (time_progress (locations (automata model ! i) ! l))"\<close>

definition inv where
  "inv i l \<equiv> the_default true
    (time_progress (the (find (\<lambda>loc. location.name loc = l) (locations (N i)))))"

definition
  "n_ps = length (elements (system model))"

definition
  "type_of x \<equiv> map_option variable_declaration.type
    (find (\<lambda>decl. variable_declaration.name decl = x) (variables model))"

definition bounded :: "dstate \<Rightarrow> bool" where
  "bounded s \<equiv> \<forall>x \<in> dom s.
    case type_of x of
      Some (TBounded b) \<Rightarrow> lower_bound b \<le> the (s x) \<and> the (s x) \<le> upper_bound b
    | _ \<Rightarrow> False"

definition get_upds where
  "get_upds destination \<equiv> let assignments = assignments destination in
    map (\<lambda>a. ((ref a, value a), index a))
      (filter (\<lambda>a. \<exists>bounds. type_of (ref a) = Some (TBounded bounds)) assignments)"

\<comment> \<open>This is clearly more restrictive than JANI\<close>
definition get_resets :: "destination \<Rightarrow> identifier list" where
  "get_resets destination \<equiv> let assignments = assignments destination in
    map (\<lambda>a. ref a) (filter (\<lambda>a. type_of (ref a) = Some TClock) assignments)"

definition is_weak where
  "is_weak p a \<equiv>
    a \<in> set (input_enable (elements (system model) ! p))"

abbreviation sort_upds where
  "sort_upds upds_idxs \<equiv> map fst (sort_key snd upds_idxs)"

definition transient_vars_upds where
  "transient_vars_upds \<equiv> List.map_filter (\<lambda>var_decl.
    if transient var_decl then
      Some (variable_declaration.name var_decl, the (initial_value var_decl))
    else None
  ) (variables model)"

inductive step ::
  "identifier list \<Rightarrow> dstate \<Rightarrow> cstate \<Rightarrow> label \<Rightarrow> identifier list \<Rightarrow> dstate \<Rightarrow> cstate \<Rightarrow> bool"
("\<langle>_, _, _\<rangle> \<rightarrow>\<^bsub>_\<^esub> \<langle>_, _, _\<rangle>" [61,61,61,61,61] 61)
where
  step_t:
    "\<lbrakk>
      ''target invariant'' \<bar> \<forall>p < n_ps. is_bval s (u \<oplus> d) (inv p (L ! p)) True;
      ''nonnegative''      \<bar> d \<ge> 0;
      ''bounded''          \<bar> bounded s
     \<rbrakk>
    \<Longrightarrow> \<langle>L, s, u\<rangle> \<rightarrow>\<^bsub>Del\<^esub> \<langle>L, s, u \<oplus> d\<rangle>" |
  step_int:
    "\<lbrakk>
      TRANS ''edge'' \<bar> e \<in> set (edges (N p));
      TRANS ''silent'' \<bar> action e = None;
      ''guard''      \<bar> is_bval s u (guard e) True;
      ''target invariant'' \<bar> \<forall>p < n_ps. is_bval s u' (inv p (L' ! p)) True; \<comment> \<open>XXX: this is not JANI\<close>
      ''destination'' \<bar> destinations e = [destination];
      ''loc''           \<bar> L!p = edge.location e;
      ''range''         \<bar> p < length L;
      ''new loc''       \<bar> L' = L[p := destination.location destination];
      ''new valuation'' \<bar> u' = [get_resets destination\<rightarrow>0]u;
      ''is_upd''        \<bar> is_upds s (sort_upds (get_upds destination)) s';
      ''transients''    \<bar> is_upds s' transient_vars_upds s'';
      ''bounded''       \<bar> bounded s''
    \<rbrakk>
    \<Longrightarrow> \<langle>L, s, u\<rangle> \<rightarrow>\<^bsub>Internal\<^esub> \<langle>L', s'', u'\<rangle>" |
  step_sync:
    "\<lbrakk>
      ''sync'' \<bar> sync \<in> set (syncs (system model));
      ''enabled'' \<bar> (\<forall>p<n_ps. \<forall>a. synchronise sync ! p = Some a \<and> \<not> is_weak p a \<longrightarrow> p \<in> set ps);
      ''only syncs'' \<bar> (\<forall>p<n_ps. synchronise sync ! p = None \<longrightarrow> p \<notin> set ps);
      ''actions'' \<bar> (\<forall>p<n_ps. \<forall>a. synchronise sync ! p = Some a \<longrightarrow> as p = a);
      TRANS ''edges'' \<bar> (\<forall>p\<in>set ps. es p \<in> set (edges (N p)));
      TRANS ''actions'' \<bar> (\<forall>p\<in>set ps. action (es p) = Some (as p));
      TRANS ''guards'' \<bar> (\<forall>p\<in>set ps. guard (es p) = gs p);
      TRANS ''locs'' \<bar> (\<forall>p\<in>set ps. location (es p) = L ! p);
      TRANS ''destinations'' \<bar> (\<forall>p\<in>set ps. destinations (es p) = [ds p]);
      TRANS ''new locs'' \<bar> (\<forall>p\<in>set ps. destination.location (ds p) = ls' p);
      ''guards''    \<bar> \<forall>p\<in>set ps. is_bval s u (gs p) True;
      ''maximal'' \<bar> \<forall>p<n_ps. \<forall>e \<in> set (edges (N p)). \<forall>a.
        p \<notin> set ps \<and> synchronise sync ! p = Some a \<and> is_weak p a \<and>
        location e = L ! p \<and> action e = Some a \<longrightarrow>
        \<not> is_bval s u (guard e) True;
      ''target invariant'' \<bar> \<forall>p<n_ps. is_bval s u' (inv p (L' ! p)) True; \<comment> \<open>XXX: this is not JANI\<close>
      SEL ''range''      \<bar> set ps \<subseteq> {0..<n_ps};
      SEL ''sublist'' \<bar> subseq ps [0..<n_ps];
      ''new loc'' \<bar> L' = fold (\<lambda>p L . L[p := ls' p]) ps L;
      ''new valuation'' \<bar> u' = [concat (map (get_resets o ds) ps)\<rightarrow>0]u;
      ''upds''    \<bar> is_upds s (sort_upds (concat (map (get_upds o ds) ps))) s';
      ''transients'' \<bar> is_upds s' transient_vars_upds s''; \<comment> \<open>Could also be expressed as a \<open>fold\<close>\<close>
      ''bounded'' \<bar> bounded s''
    \<rbrakk>
    \<Longrightarrow> \<langle>L, s, u\<rangle> \<rightarrow>\<^bsub>Sync sync\<^esub> \<langle>L', s'', u'\<rangle>"
lemmas [intro?] = step_u.intros[unfolded TAG_def]
print_statement step_u.intros[unfolded TAG_def]
text \<open>Comments:
\<^item> Should there be an error transition + state if states run of bounds or updates are undefined?
Then one could run a reachability check for the error state.
\<^item> Should the state be total?
\<^item> Note that intermediate states are allowed to run out of bounds
\<^item> We do not explicitly enforce that the same process cannot appear multiple times in a sync
\<^item> We do not explicitly enforce that process and indices and actions names are valid in syncs
\<close>

definition steps_u ::
  "identifier list \<Rightarrow> dstate \<Rightarrow> cstate \<Rightarrow> identifier list \<Rightarrow> dstate \<Rightarrow> cstate \<Rightarrow> bool"
("\<langle>_, _, _\<rangle> \<rightarrow>* \<langle>_, _, _\<rangle>" [61,61,61,61] 61)
where
  "\<langle>L, s, u\<rangle> \<rightarrow>* \<langle>L', s', u'\<rangle> \<equiv>
    (\<lambda> (L, s, u) (L', s', u'). \<exists>a. \<langle>L, s, u\<rangle> \<rightarrow>\<^bsub>a\<^esub> \<langle>L', s', u'\<rangle>)\<^sup>*\<^sup>* (L, s, u) (L', s', u')"

end

end (* Theory *)