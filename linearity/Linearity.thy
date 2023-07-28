theory Linearity
  imports
    Main
begin

section \<open>Syntax\<close>

type_synonym name_atom = string
datatype name =
  FName name_atom
| BName nat nat (* the first index is the binder, the second is the variable within the binder *)

type_synonym var_atom = string
type_synonym base_val = nat
datatype val =
  Base base_val
| FVar var_atom
| BVar nat

datatype process =
  Inaction
| Output name val process
| Input name process (* binds a variable *)
| Composition process process
| Restriction process (* binds two names *)

subsection \<open>Opening\<close>

fun open_var_val where
  \<open>open_var_val k x (Base v) = Base v\<close>
| \<open>open_var_val k x (FVar y) = FVar y\<close>
| \<open>open_var_val k x (BVar i) = (if i = k then x else BVar i)\<close>

fun open_var_rec where
  \<open>open_var_rec k x Inaction = Inaction\<close>
| \<open>open_var_rec k x (Output y v P) = Output y (open_var_val k x v) (open_var_rec k x P)\<close>
| \<open>open_var_rec k x (Input y P) = Input y (open_var_rec (Suc k) x P)\<close>
| \<open>open_var_rec k x (Composition P Q) = Composition (open_var_rec k x P) (open_var_rec k x Q)\<close>
| \<open>open_var_rec k x (Restriction P) = Restriction (open_var_rec k x P)\<close>

definition open_var where
  \<open>open_var x P \<equiv> open_var_rec 0 x P\<close>

fun open_names_name where
  \<open>open_names_name k xs (FName y) = FName y\<close>
| \<open>open_names_name k xs (BName i j) = (if i = k then xs ! j else BName i j)\<close>

fun open_names_rec where
  \<open>open_names_rec k xs Inaction = Inaction\<close>
| \<open>open_names_rec k xs (Output y v P) = Output (open_names_name k xs y) v (open_names_rec k xs P)\<close>
| \<open>open_names_rec k xs (Input y P) = Input (open_names_name k xs y) (open_names_rec k xs P)\<close>
| \<open>open_names_rec k xs (Composition P Q) = Composition (open_names_rec k xs P) (open_names_rec k xs Q)\<close>
| \<open>open_names_rec k xs (Restriction P) = Restriction (open_names_rec (Suc k) xs P)\<close>

definition open_names where
  \<open>open_names xs P \<equiv> open_names_rec 0 xs P\<close>

subsection \<open>Closing\<close>

fun close_var_val where
  \<open>close_var_val k x (Base v) = Base v\<close>
| \<open>close_var_val k x (FVar y) = (if x = y then BVar k else FVar y)\<close>
| \<open>close_var_val k x (BVar i) = BVar i\<close>

fun close_var_rec where
  \<open>close_var_rec k x Inaction = Inaction\<close>
| \<open>close_var_rec k x (Output y v P) = Output y (close_var_val k x v) (close_var_rec k x P)\<close>
| \<open>close_var_rec k x (Input y P) = Input y (close_var_rec (Suc k) x P)\<close>
| \<open>close_var_rec k x (Composition P Q) = Composition (close_var_rec k x P) (close_var_rec k x Q)\<close>
| \<open>close_var_rec k x (Restriction P) = Restriction (close_var_rec k x P)\<close>

definition close_var where
  \<open>close_var x P \<equiv> close_var_rec 0 x P\<close>

fun close_name_name where
  \<open>close_name_name k x a (FName y) = (if x = y then BName k a else FName y)\<close>
| \<open>close_name_name k x a (BName i j) = BName i j\<close>

fun close_name_rec where
  \<open>close_name_rec k x a Inaction = Inaction\<close>
| \<open>close_name_rec k x a (Output y v P) = Output (close_name_name k x a y) v (close_name_rec k x a P)\<close>
| \<open>close_name_rec k x a (Input y P) = Input (close_name_name k x a y) (close_name_rec k x a P)\<close>
| \<open>close_name_rec k x a (Composition P Q) = Composition (close_name_rec k x a P) (close_name_rec k x a Q)\<close>
| \<open>close_name_rec k x a (Restriction P) = Restriction (close_name_rec (Suc k) x a P)\<close>

definition close_name where
  \<open>close_name x P \<equiv> close_name_rec 0 x P\<close>

subsection \<open>Free variables\<close>

fun free_vars_val where
  \<open>free_vars_val (Base _) = {}\<close>
| \<open>free_vars_val (FVar x) = {x}\<close>
| \<open>free_vars_val (BVar _) = {}\<close>

fun free_vars where
  \<open>free_vars Inaction = {}\<close>
| \<open>free_vars (Output x v P) = free_vars_val v \<union> free_vars P\<close>
| \<open>free_vars (Input x P) = free_vars P\<close>
| \<open>free_vars (Composition P Q) = free_vars P \<union> free_vars Q\<close>
| \<open>free_vars (Restriction P) = free_vars P\<close>

fun free_names_name where
  \<open>free_names_name (FName x) = {FName x}\<close>
| \<open>free_names_name (BName _ _) = {}\<close>

fun free_names where
  \<open>free_names Inaction = {}\<close>
| \<open>free_names (Output x v P) = free_names_name x \<union> free_names P\<close>
| \<open>free_names (Input x P) = free_names_name x \<union> free_names P\<close>
| \<open>free_names (Composition P Q) = free_names P \<union> free_names Q\<close>
| \<open>free_names (Restriction P) = free_names P\<close>

subsection \<open>Local closure\<close>

inductive lc_val where
  LCBase[intro]: \<open>lc_val (Base v)\<close>
| LCFVar[intro]: \<open>lc_val (FVar x)\<close>

inductive lc_name where
  LCFName[intro]: \<open>lc_name (FName x)\<close>

inductive lc where
  LCInaction[intro]: \<open>lc Inaction\<close>
| LCOutput[intro]: \<open>lc_name x \<Longrightarrow> lc_val v \<Longrightarrow> lc P \<Longrightarrow> lc (Output x v P)\<close>
| LCInput[intro]: \<open>lc_name x \<Longrightarrow> \<exists>L. \<forall>y. y \<notin> L \<longrightarrow> lc (open_var (FVar y) P) \<Longrightarrow> lc (Input x P)\<close>
| LCComposition[intro]: \<open>lc P \<Longrightarrow> lc Q \<Longrightarrow> lc (Composition P Q)\<close>
| LCRestriction[intro]: \<open>\<exists>L. \<forall>x y. (x \<notin> L \<and> y \<notin> L) \<longrightarrow> lc (open_names [x,y] P) \<Longrightarrow> lc (Restriction P)\<close>

definition input_body where
  \<open>input_body P \<equiv> \<exists>L. \<forall>y. y \<notin> L \<longrightarrow> lc (open_var (FVar y) P)\<close>

lemma lc_input_iff_input_body:
  \<open>lc_name x \<Longrightarrow> lc (Input x P) \<longleftrightarrow> input_body P\<close>
  using LCInput input_body_def by blast

definition restriction_body where
  \<open>restriction_body P \<equiv> \<exists>L. \<forall>x y. (x \<notin> L \<and> y \<notin> L) \<longrightarrow> lc (open_names [x,y] P)\<close>

lemma lc_restriction_iff_restriction_body:
  \<open>lc (Restriction P) \<longleftrightarrow> restriction_body P\<close>
  using LCRestriction restriction_body_def by blast

subsection \<open>Substitution\<close>

fun subst_var_val where
  \<open>subst_var_val (Base v) y u = Base v\<close>
| \<open>subst_var_val (FVar x) y u = (if x = y then u else FVar x)\<close>
| \<open>subst_var_val (BVar i) y u = BVar i\<close>

fun subst_var where
  \<open>subst_var Inaction y u = Inaction\<close>
| \<open>subst_var (Output x v P) y u = Output x (subst_var_val v y u) (subst_var P y u)\<close>
| \<open>subst_var (Input x P) y u = Input x (subst_var P y u)\<close>
| \<open>subst_var (Composition P Q) y u = Composition (subst_var P y u) (subst_var Q y u)\<close>
| \<open>subst_var (Restriction P) y u = Restriction (subst_var P y u)\<close>

fun subst_name_name where
  \<open>subst_name_name (FName x) y u = (if x = y then u else FName x)\<close>
| \<open>subst_name_name (BName i j) y u = BName i j\<close>

fun subst_name where
  \<open>subst_name Inaction y u = Inaction\<close>
| \<open>subst_name (Output x v P) y u = Output (subst_name_name x y u) v (subst_name P y u)\<close>
| \<open>subst_name (Input x P) y u = Input (subst_name_name x y u) (subst_name P y u)\<close>
| \<open>subst_name (Composition P Q) y u = Composition (subst_name P y u) (subst_name Q y u)\<close>
| \<open>subst_name (Restriction P) y u = Restriction (subst_name P y u)\<close>

subsection \<open>Properties\<close>

section \<open>Semantics\<close>

subsection \<open>Contexts\<close>

datatype ctx =
  CHole
| CInaction
| COutput name val ctx
| CInput name ctx (* binds a variable *)
| CComposition ctx ctx
| CRestriction ctx (* binds two names *)

fun apply_ctx where
  \<open>apply_ctx CHole P = P\<close>
| \<open>apply_ctx CInaction P = Inaction\<close>
| \<open>apply_ctx (COutput x v C) P = Output x v (apply_ctx C P)\<close>
| \<open>apply_ctx (CInput x C) P = Input x (apply_ctx C P)\<close>
| \<open>apply_ctx (CComposition C D) P = Composition (apply_ctx C P) (apply_ctx D P)\<close>
| \<open>apply_ctx (CRestriction C) P = Restriction (apply_ctx C P)\<close>

fun holes_in_ctx :: \<open>ctx \<Rightarrow> nat\<close> where
  \<open>holes_in_ctx CHole = 1\<close>
| \<open>holes_in_ctx CInaction = 0\<close>
| \<open>holes_in_ctx (COutput _ _ C) = holes_in_ctx C\<close>
| \<open>holes_in_ctx (CInput _ C) = holes_in_ctx C\<close>
| \<open>holes_in_ctx (CComposition C D) = holes_in_ctx C + holes_in_ctx D\<close>
| \<open>holes_in_ctx (CRestriction C) = holes_in_ctx C\<close>

definition wf_ctx where \<open>wf_ctx C \<equiv> holes_in_ctx C = 1\<close>

subsection \<open>Structural congruence\<close>

inductive struct_cong (\<open>_ \<^bold>\<equiv> _\<close>) where
  ScParComm[intro]: \<open>lc P \<Longrightarrow> lc Q \<Longrightarrow> (Composition P Q) \<^bold>\<equiv> (Composition Q P)\<close>
| ScParAssoc[intro]: \<open>lc P \<Longrightarrow> lc Q \<Longrightarrow> lc R \<Longrightarrow> (Composition (Composition P Q) R) \<^bold>\<equiv> (Composition P (Composition Q R))\<close>
| ScParInact[intro]: \<open>lc P \<Longrightarrow> (Composition P Inaction) \<^bold>\<equiv> P\<close>
| ScResPar[intro]: \<open>lc P \<Longrightarrow> lc Q \<Longrightarrow> (Composition (Restriction P) Q) \<^bold>\<equiv> (Restriction (Composition P Q))\<close>
| ScResInact[intro]: \<open>(Restriction Inaction) \<^bold>\<equiv> Inaction\<close>

lemma struct_cong_lc[simp]: \<open>P \<^bold>\<equiv> Q \<Longrightarrow> lc P \<and> lc Q\<close>
  by (induction rule: struct_cong.induct) auto

subsection \<open>Operational semantics\<close>

inductive semantics (\<open>_ \<longlongrightarrow> _\<close>) where
  RCom[intro]: \<open>lc_val v \<Longrightarrow> lc P \<Longrightarrow> lc Q \<Longrightarrow> lc R \<Longrightarrow>
          (Restriction (Composition (Composition (Output (BName 0 0) v P) (Input (BName 0 1) Q)) R))
           \<longlongrightarrow> (Restriction (Composition (Composition P (open_var v Q)) R))\<close>
| RRes[intro]: \<open>P \<longlongrightarrow> Q \<Longrightarrow> (Restriction P) \<longlongrightarrow> (Restriction Q)\<close>
| RPar[intro]: \<open>lc R \<Longrightarrow> P \<longlongrightarrow> Q \<Longrightarrow> (Composition P R) \<longlongrightarrow> (Composition Q R)\<close>
| RStruct[intro]: \<open>P \<^bold>\<equiv> P' \<Longrightarrow> P' \<longlongrightarrow> Q' \<Longrightarrow> Q \<^bold>\<equiv> Q' \<Longrightarrow> P \<longlongrightarrow> Q\<close>

lemma semantics_lc[simp]: \<open>P \<longlongrightarrow> Q \<Longrightarrow> lc P \<and> lc Q\<close>
  by (induction rule: semantics.induct) auto

subsection \<open>Well-formed processes\<close>

fun prefixed_at where
  \<open>prefixed_at x (Output y _ _) = (x = y)\<close>
| \<open>prefixed_at x (Input y _) = (x = y)\<close>
| \<open>prefixed_at _ _ = False\<close>

fun append_res where
  \<open>append_res 0 P = Restriction P\<close>
| \<open>append_res (Suc n) P = append_res n (Restriction P)\<close>

definition wf_process where
  \<open>wf_process P \<equiv> \<forall>Q. (P \<^bold>\<equiv> Q) \<and> (\<exists>n X Y Z. Q = append_res n (Composition (Composition X Y) Z))
    \<longrightarrow> (\<forall>x y. prefixed_at x P \<and> prefixed_at y Q
        \<longrightarrow> ((\<exists>P' a. P = Output x a P') \<and> (\<exists>Q'. Q = Input y Q')))\<close>

section \<open>Session types\<close>

datatype type =
  TEnd
| TBase
| TOut type
| TIn type

fun un where
  \<open>un TEnd = True\<close>
| \<open>un TBase = True\<close>
| \<open>un _ = False\<close>

subsection \<open>Duality\<close>

fun dual where
  \<open>dual TEnd = Some TEnd\<close>
| \<open>dual TBase = None\<close>
| \<open>dual (TOut S) = Option.bind (dual S) (Some \<circ> TIn)\<close>
| \<open>dual (TIn S) = Option.bind (dual S) (Some \<circ> TOut)\<close>

subsection \<open>Type contexts\<close>

datatype ctx_elem =
  CVar var_atom
| CName name_atom

type_synonym type_ctx = \<open>(ctx_elem, type) map\<close>

definition un_ctx :: \<open>type_ctx \<Rightarrow> bool\<close> where
  \<open>un_ctx \<Gamma> \<equiv> \<forall>T \<in> ran \<Gamma>. un T\<close>

inductive split :: \<open>type_ctx \<Rightarrow> type_ctx \<Rightarrow> type_ctx \<Rightarrow> bool\<close> (\<open>_ \<circle> _ = _\<close>) where
  SplitEmpty[intro]: \<open>Map.empty \<circle> Map.empty = Map.empty\<close>
| SplitUn[intro]: \<open>un T \<Longrightarrow> \<Gamma>\<^sub>1 \<circle> \<Gamma>\<^sub>2 = \<Gamma> \<Longrightarrow> \<Gamma>\<^sub>1(x \<mapsto> T) \<circle> \<Gamma>\<^sub>2(x \<mapsto> T) = (\<Gamma>(x \<mapsto> T))\<close>
| SplitLinL[intro]: \<open>\<Gamma>\<^sub>1 \<circle> \<Gamma>\<^sub>2 = \<Gamma> \<Longrightarrow> \<Gamma>\<^sub>1(x \<mapsto> S) \<circle> \<Gamma>\<^sub>2 = (\<Gamma>(x \<mapsto> S))\<close>
| SplitLinR[intro]: \<open>\<Gamma>\<^sub>1 \<circle> \<Gamma>\<^sub>2 = \<Gamma> \<Longrightarrow> \<Gamma>\<^sub>1 \<circle> \<Gamma>\<^sub>2(x \<mapsto> S) = (\<Gamma>(x \<mapsto> S))\<close>

lemma split_commute: \<open>\<Gamma>\<^sub>1 \<circle> \<Gamma>\<^sub>2 = \<Gamma> \<Longrightarrow> \<Gamma>\<^sub>2 \<circle> \<Gamma>\<^sub>1 = \<Gamma>\<close>
  by (induction rule: split.induct) blast+

inductive update :: \<open>type_ctx \<Rightarrow> name \<Rightarrow> type \<Rightarrow> type_ctx \<Rightarrow> bool\<close> (\<open>_ \<^bold>+ _ : _ = _\<close>) where
  UpdateName[intro]: \<open>x = FName y \<Longrightarrow> (CName y,U) \<notin> Map.graph \<Gamma> \<Longrightarrow> \<Gamma> \<^bold>+ x : T = (\<Gamma>(CName y \<mapsto> T))\<close>
| UpdateUn[intro]: \<open>x = FName y \<Longrightarrow> un T \<Longrightarrow> \<Gamma>(CName y \<mapsto> T) \<^bold>+ x : T = (\<Gamma>(CName y \<mapsto> T))\<close>

lemma update_lc_ctx[simp]: \<open>\<Gamma> \<^bold>+ x : T = \<Gamma>' \<Longrightarrow> lc_name x\<close>
  by (induction rule: update.induct) auto

subsection \<open>Typing\<close>

inductive typing_values :: \<open>type_ctx \<Rightarrow> val \<Rightarrow> type \<Rightarrow> bool\<close> (\<open>_ \<turnstile>\<^sub>v _ : _\<close>) where
  TBase[intro]: \<open>un_ctx \<Gamma> \<Longrightarrow> \<Gamma> \<turnstile>\<^sub>v Base a : TBase\<close>
| TVar[intro]: \<open>un_ctx \<Gamma> \<Longrightarrow> \<Gamma>(CVar v \<mapsto> TBase) \<turnstile>\<^sub>v FVar v : TBase\<close>

lemma typing_values_lc[simp]: \<open>\<Gamma> \<turnstile>\<^sub>v v : T \<Longrightarrow> lc_val v\<close>
  by (induction rule: typing_values.induct) auto

inductive typing_names (\<open>_ \<turnstile>\<^sub>n _ : _\<close>) where
  TName[intro]: \<open>un_ctx \<Gamma> \<Longrightarrow> \<Gamma>(CName x \<mapsto> T) \<turnstile>\<^sub>n FName x : T\<close>

lemma typing_names_lc[simp]: \<open>\<Gamma> \<turnstile>\<^sub>n x : T \<Longrightarrow> lc_name x\<close>
  by (induction rule: typing_names.induct) auto

inductive typing (\<open>_ \<turnstile> _\<close>) where
  TInaction[intro]: \<open>un_ctx \<Gamma> \<Longrightarrow> \<Gamma> \<turnstile> Inaction\<close>
| TPar[intro]: \<open>\<Gamma>\<^sub>1 \<turnstile> P \<Longrightarrow> \<Gamma>\<^sub>2 \<turnstile> Q \<Longrightarrow> \<Gamma>\<^sub>1 \<circle> \<Gamma>\<^sub>2 = \<Gamma> \<Longrightarrow> \<Gamma> \<turnstile> (Composition P Q)\<close>
| TRes[intro]: \<open>dual T = Some T' \<Longrightarrow> (\<Gamma>(CName x \<mapsto> T, CName y \<mapsto> T')) \<turnstile> P
      \<Longrightarrow> \<Gamma> \<turnstile> (Restriction (close_name y 1 (close_name x 0 P)))\<close>
| TOut[intro]: \<open>\<Gamma>\<^sub>1 \<turnstile>\<^sub>n x : (TOut T)
      \<Longrightarrow> \<Gamma>\<^sub>2 \<turnstile>\<^sub>v v : TBase
      \<Longrightarrow> \<Gamma>\<^sub>3 \<^bold>+ x : T = \<Gamma>' \<Longrightarrow> \<Gamma>' \<turnstile> P
      \<Longrightarrow> \<Gamma>\<^sub>1 \<circle> \<Gamma>\<^sub>2 = \<Gamma>\<^sub>1\<^sub>2 \<Longrightarrow> \<Gamma>\<^sub>1\<^sub>2 \<circle> \<Gamma>\<^sub>3 = \<Gamma> \<Longrightarrow> \<Gamma> \<turnstile> (Output x v P)\<close>
| TIn[intro]: \<open>\<Gamma>\<^sub>1 \<turnstile>\<^sub>n x : (TIn U)
          \<Longrightarrow> \<Gamma>\<^sub>2(CVar l \<mapsto> TBase) \<^bold>+ x : U = \<Gamma>\<^sub>2' \<Longrightarrow> \<Gamma>\<^sub>2' \<turnstile> P
          \<Longrightarrow> (\<Gamma>\<^sub>1 \<circle> \<Gamma>\<^sub>2 = \<Gamma>) \<Longrightarrow> \<Gamma> \<turnstile> (Input x (close_var l P))\<close>

lemma typing_lc: \<open>\<Gamma> \<turnstile> P \<Longrightarrow> lc P\<close>
proof (induction rule: typing.induct)
  case (TRes T T' \<Gamma> x y P)
  then show ?case
    by blast
next
  case (TOut \<Gamma>\<^sub>1 x T \<Gamma>\<^sub>2 v \<Gamma>\<^sub>3 \<Gamma>' P \<Gamma>\<^sub>1\<^sub>2 \<Gamma>)
  then show ?case
    by (simp add: LCOutput)
next
  case (TIn \<Gamma>\<^sub>1 x U \<Gamma>\<^sub>2 l \<Gamma>\<^sub>2' P \<Gamma>)
  then show ?case
    using typing_names_lc by blast
qed auto

lemma typing_add_unrestricted_name: \<open>\<Gamma> \<turnstile> P \<Longrightarrow> un T \<Longrightarrow> \<Gamma>(CName x \<mapsto> T) \<turnstile> P\<close>
proof (induction rule: typing.induct)
  case (TInaction \<Gamma>)
  then show ?case
    by (smt (verit, best) fun_upd_same fun_upd_upd insert_iff map_upd_Some_unfold mem_Collect_eq name.inject(1) ranI ran_restrictD restrict_complement_singleton_eq restrict_map_insert restrict_upd_same typing.TInaction un_ctx_def)
next
  case (TPar \<Gamma>\<^sub>1 P \<Gamma>\<^sub>2 Q \<Gamma>)
  then show ?case
    by blast
next
  case (TRes T T' \<Gamma> x y P)
  then show ?case
    by (smt (verit, best) fun_upd_twist fun_upd_upd typing.TRes)
next
  case (TOut \<Gamma>\<^sub>1 x' T' \<Gamma>\<^sub>2 v \<Gamma>\<^sub>3 \<Gamma>' P \<Gamma>\<^sub>1\<^sub>2 \<Gamma>)
  then show ?case
    sorry
next
  case (TIn \<Gamma>\<^sub>1 x U \<Gamma>\<^sub>2 l \<Gamma>\<^sub>2' P \<Gamma>)
  then show ?case
    sorry
qed

lemma typing_add_unrestricted_var: \<open>\<Gamma> \<turnstile> P \<Longrightarrow> un T \<Longrightarrow> \<Gamma>(CVar x \<mapsto> T) \<turnstile> P\<close>
proof (induction rule: typing.induct)
  case (TInaction \<Gamma>)
  then show ?case
    by (smt (verit, ccfv_SIG) fun_upd_same fun_upd_upd map_upd_Some_unfold ranI ran_restrictD restrict_complement_singleton_eq restrict_map_insert restrict_upd_same typing.TInaction un_ctx_def)
next
  case (TPar \<Gamma>\<^sub>1 P \<Gamma>\<^sub>2 Q \<Gamma>)
  then show ?case
    by blast
next
  case (TRes T T' \<Gamma> x y P)
  then show ?case
    by (smt (verit, ccfv_SIG) ctx_elem.distinct(2) fun_upd_twist typing.TRes)
next
  case (TOut \<Gamma>\<^sub>1 x T \<Gamma>\<^sub>2 v \<Gamma>\<^sub>3 \<Gamma>' P \<Gamma>\<^sub>1\<^sub>2 \<Gamma>)
  then show ?case
    sorry
next
  case (TIn \<Gamma>\<^sub>1 x U \<Gamma>\<^sub>2 l \<Gamma>\<^sub>2' P \<Gamma>)
  then show ?case
    sorry
qed

lemma typing_add_restricted_name:
  assumes \<open>\<Gamma> \<turnstile> P\<close> and \<open>FName x \<notin> free_names P\<close>
  shows \<open>\<forall>T. (CName x, TOut T) \<notin> Map.graph \<Gamma>\<close>
    and \<open>\<forall>T. (CName x, TIn T) \<notin> Map.graph \<Gamma>\<close>
    and \<open>\<Gamma> = \<Gamma>'(CName x \<mapsto> T) \<Longrightarrow> \<Gamma>' \<turnstile> P\<close>
  sorry

lemma typing_struct_cong: \<open>P \<^bold>\<equiv> Q \<Longrightarrow> \<Gamma> \<turnstile> P \<Longrightarrow> \<Gamma> \<turnstile> Q\<close>
proof (induction rule: struct_cong.induct)
  case (ScParComm P Q)
  from ScParComm.prems show ?case
  proof (cases rule: typing.cases)
    case (TPar \<Gamma>\<^sub>1 \<Gamma>\<^sub>2)
    then show ?thesis
      using split_commute by blast
  qed
next
  case (ScParAssoc P Q R)
  from ScParAssoc.prems show ?case
  proof (cases rule: typing.cases)
    case *: (TPar \<Gamma>\<^sub>1 \<Gamma>\<^sub>2)
    from *(1) show ?thesis
    proof (cases rule: typing.cases)
      case (TPar \<Gamma>\<^sub>3 \<Gamma>\<^sub>4)
      then show ?thesis
        using *(2-3) split_commute typing.TPar[of \<Gamma>\<^sub>1 P \<Gamma>\<^sub>2 \<open>Composition Q R\<close> \<Gamma>]
        sorry
    qed
  qed
next
  case (ScParInact P)
  then show ?case sorry
next
  case (ScResPar P Q)
  then show ?case sorry
next
  case ScResInact
  then show ?case sorry
qed

lemma typing_subst_var: \<open>\<Gamma>\<^sub>1 \<turnstile>\<^sub>v v : T \<Longrightarrow> \<Gamma>\<^sub>2(CVar x \<mapsto> T) \<turnstile> P \<Longrightarrow> \<Gamma>\<^sub>1 \<circle> \<Gamma>\<^sub>2 = \<Gamma> \<Longrightarrow> \<Gamma> \<turnstile> (subst_var P x v)\<close>
  sorry

lemma composition_semantics_cases[elim]:
  assumes \<open>(Composition A B) \<longlongrightarrow> (Composition C D)\<close>
    and \<open>A = C \<Longrightarrow> B \<longlongrightarrow> D \<Longrightarrow> R\<close>
    and \<open>B = D \<Longrightarrow> A \<longlongrightarrow> C \<Longrightarrow> R\<close>
  shows \<open>R\<close>
  using assms
proof (cases rule: semantics.cases)
  case RPar
  then show ?thesis using assms by simp
next
  case *: (RStruct P' Q')
  from *(2) show ?thesis
  proof (cases rule: semantics.cases)
    case (RCom v P Q R)
    then show ?thesis using assms *
      sorry
  next
    case (RRes P Q)
    then show ?thesis sorry
  next
    case (RPar R P Q)
    then show ?thesis sorry
  next
    case (RStruct P'' Q'')
    then show ?thesis using assms * sorry
  qed
qed

theorem subject_reduction: \<open>\<Gamma> \<turnstile> P \<Longrightarrow> P \<longlongrightarrow> Q \<Longrightarrow> \<Gamma> \<turnstile> Q\<close>
proof (induction arbitrary: Q rule: typing.induct)
  case (TInaction \<Gamma>)
  then show ?case
    using semantics.simps struct_cong.simps by blast
next
  case (TPar \<Gamma>\<^sub>1 P \<Gamma>\<^sub>2 Q' \<Gamma> Q)
  then show ?case
  proof (cases Q)
    case (Composition P' Q'')
    then show ?thesis
      using RPar TPar by blast
  qed (smt (verit, del_insts) process.distinct semantics.simps struct_cong.simps)+
next
  case (TRes T T' \<Gamma> x y P)
  from TRes.prems show ?case
  proof (cases Q)
    case (Restriction R)
    then show ?thesis using TRes
      sorry
  qed (smt (verit, best) process.distinct process.simps(20) semantics.simps struct_cong.simps)+
next
  case (TOut \<Gamma>\<^sub>1 x T \<Gamma>\<^sub>2 v \<Gamma>\<^sub>3 \<Gamma>' P \<Gamma>\<^sub>1\<^sub>2 \<Gamma>)
  then show ?case
    by (smt (verit, best) process.distinct(11) process.distinct(13) semantics.simps struct_cong.simps)
next
  case (TIn \<Gamma>\<^sub>1 x U \<Gamma>\<^sub>2 l \<Gamma>\<^sub>2' P \<Gamma>)
  then show ?case
    by (smt (verit, best) process.distinct(17) process.simps(20) semantics.simps struct_cong.simps)
qed

theorem type_safety: \<open>Map.empty \<turnstile> P \<Longrightarrow> wf_process P\<close>
proof (induction P rule: typing.induct)
  case (TOut \<Gamma>\<^sub>1 x T \<Gamma>\<^sub>2 v \<Gamma>\<^sub>3 \<Gamma>' P \<Gamma>\<^sub>1\<^sub>2 \<Gamma>)
  then show ?case unfolding wf_process_def
  proof (clarify)
    fix Q x' y n X Y Z
    assume \<open>(Output x v P) \<^bold>\<equiv> (append_res n (Composition (Composition X Y) Z))\<close>
           \<open>prefixed_at x' (Output x v P)\<close>
    then show \<open>(\<exists>P' a. Output x v P = Output x' a P') \<and> (\<exists>Q'. append_res n (Composition (Composition X Y) Z) = Input y Q')\<close>
      using struct_cong.simps by blast
  qed
next
  case (TIn \<Gamma>\<^sub>1 x U \<Gamma>\<^sub>2 l \<Gamma>\<^sub>2' P \<Gamma>)
  then show ?case unfolding wf_process_def
    by (smt (verit, ccfv_SIG) prefixed_at.simps(4) process.distinct(17) struct_cong.simps)
qed (auto simp add: wf_process_def)

corollary \<open>Map.empty \<turnstile> P \<Longrightarrow> P \<longlongrightarrow> Q \<Longrightarrow> wf_process Q\<close>
  using subject_reduction type_safety by blast

end