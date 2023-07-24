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

fun open_name_name where
  \<open>open_name_name k xs (FName y) = FName y\<close>
| \<open>open_name_name k xs (BName i j) = (if i = k then xs ! j else BName i j)\<close>

fun open_name_rec where
  \<open>open_name_rec k xs Inaction = Inaction\<close>
| \<open>open_name_rec k xs (Output y v P) = Output (open_name_name k xs y) v (open_name_rec k xs P)\<close>
| \<open>open_name_rec k xs (Input y P) = Input (open_name_name k xs y) (open_name_rec k xs P)\<close>
| \<open>open_name_rec k xs (Composition P Q) = Composition (open_name_rec k xs P) (open_name_rec k xs Q)\<close>
| \<open>open_name_rec k xs (Restriction P) = Restriction (open_name_rec (Suc k) xs P)\<close>

definition open_name where
  \<open>open_name xs P \<equiv> open_name_rec 0 xs P\<close>

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

subsection \<open>Substitution\<close>

subsection \<open>Local closure\<close>

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
  ScParComm:  \<open>(Composition P Q) \<^bold>\<equiv> (Composition Q P)\<close>
| ScParAssoc: \<open>(Composition (Composition P Q) R) \<^bold>\<equiv> (Composition P (Composition Q P))\<close>
| ScParInact: \<open>(Composition P Inaction) \<^bold>\<equiv> P\<close>
| ScResPar: \<open>(Composition (Restriction P) Q) \<^bold>\<equiv> (Restriction (Composition P Q))\<close>
| ScResInact: \<open>(Restriction Inaction) \<^bold>\<equiv> Inaction\<close>

(* for ScResPar, we probably don't need to do anything about the names being "rebound"? *)

subsection \<open>Operational semantics\<close>

inductive semantics (\<open>_ \<longlongrightarrow> _\<close>) where
  RCom: \<open>(Restriction (Composition (Composition (Output (BName 0 0) v P) (Input (BName 0 1) Q)) R))
           \<longlongrightarrow> (Restriction (Composition (Composition P (open_var v Q)) R))\<close>
| RRes: \<open>P \<longlongrightarrow> Q \<Longrightarrow> (Restriction P) \<longlongrightarrow> (Restriction Q)\<close>
| RPar: \<open>P \<longlongrightarrow> Q \<Longrightarrow> (Composition P R) \<longlongrightarrow> (Composition Q R)\<close>
| RStruct: \<open>P \<^bold>\<equiv> P' \<Longrightarrow> P' \<longlongrightarrow> Q' \<Longrightarrow> Q \<^bold>\<equiv> Q' \<Longrightarrow> P \<longlongrightarrow> Q\<close>

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

type_synonym type_ctx = \<open>(name, type) map\<close>

definition un_ctx :: \<open>type_ctx \<Rightarrow> bool\<close> where
  \<open>un_ctx \<Gamma> \<equiv> \<forall>T \<in> ran \<Gamma>. un T\<close>

inductive split :: \<open>type_ctx \<Rightarrow> type_ctx \<Rightarrow> type_ctx \<Rightarrow> bool\<close> (\<open>_ \<circle> _ = _\<close>) where
  SplitEmpty: \<open>Map.empty \<circle> Map.empty = Map.empty\<close>
| SplitUn: \<open>un T \<Longrightarrow> \<Gamma>\<^sub>1 \<circle> \<Gamma>\<^sub>2 = \<Gamma> \<Longrightarrow> \<Gamma>\<^sub>1(x \<mapsto> T) \<circle> \<Gamma>\<^sub>2(x \<mapsto> T) = (\<Gamma>(x \<mapsto> T))\<close>
| SplitLinL: \<open>\<Gamma>\<^sub>1 \<circle> \<Gamma>\<^sub>2 = \<Gamma> \<Longrightarrow> \<Gamma>\<^sub>1(x \<mapsto> S) \<circle> \<Gamma>\<^sub>2 = (\<Gamma>(x \<mapsto> S))\<close>
| SplitLinR: \<open>\<Gamma>\<^sub>1 \<circle> \<Gamma>\<^sub>2 = \<Gamma> \<Longrightarrow> \<Gamma>\<^sub>1 \<circle> \<Gamma>\<^sub>2(x \<mapsto> S) = (\<Gamma>(x \<mapsto> S))\<close>

inductive update :: \<open>type_ctx \<Rightarrow> name \<Rightarrow> type \<Rightarrow> type_ctx \<Rightarrow> bool\<close> (\<open>_ \<^bold>+ _ : _ = _\<close>) where
  UpdateName: \<open>(x,U) \<notin> Map.graph \<Gamma> \<Longrightarrow> \<Gamma> \<^bold>+ x : T = (\<Gamma>(x \<mapsto> T))\<close>
| UpdateUn: \<open>un T \<Longrightarrow> \<Gamma>(x \<mapsto> T) \<^bold>+ x : T = (\<Gamma>(x \<mapsto> T))\<close>

subsection \<open>Typing\<close>

inductive typing_values :: \<open>type_ctx \<Rightarrow> val \<Rightarrow> type \<Rightarrow> bool\<close> (\<open>_ \<turnstile>\<^sub>v _ : _\<close>) where
  TBase:  \<open>un_ctx \<Gamma> \<Longrightarrow> \<Gamma> \<turnstile>\<^sub>v Base a : TBase\<close>

inductive typing_names (\<open>_ \<turnstile>\<^sub>n _ : _\<close>) where
  TName: \<open>un_ctx \<Gamma> \<Longrightarrow> \<Gamma>(x \<mapsto> T) \<turnstile>\<^sub>n x : T\<close>

inductive typing (\<open>_ \<turnstile> _\<close>) where
  TInaction: \<open>un_ctx \<Gamma> \<Longrightarrow> \<Gamma> \<turnstile> Inaction\<close>
| TPar: \<open>\<Gamma>\<^sub>1 \<turnstile> P \<Longrightarrow> \<Gamma>\<^sub>2 \<turnstile> Q \<Longrightarrow> \<Gamma>\<^sub>1 \<circle> \<Gamma>\<^sub>2 = \<Gamma> \<Longrightarrow> \<Gamma> \<turnstile> (Composition P Q)\<close>
| TRes: \<open>dual T = Some T' \<Longrightarrow> (\<Gamma>(x \<mapsto> T, y \<mapsto> T')) \<turnstile> P \<Longrightarrow> \<Gamma> \<turnstile> (Restriction P)\<close>
| TIn: \<open>(\<Gamma>\<^sub>1 \<turnstile>\<^sub>n x : (TIn U))
          \<Longrightarrow> \<Gamma>\<^sub>2(l \<mapsto> TBase) \<^bold>+ x : U = \<Gamma>\<^sub>2'
          \<Longrightarrow> \<Gamma>\<^sub>2' \<turnstile> P
          \<Longrightarrow> (\<Gamma>\<^sub>1 \<circle> \<Gamma>\<^sub>2 = \<Gamma>)
          \<Longrightarrow> \<Gamma> \<turnstile> (Input x P)\<close>

lemma \<open>\<Gamma> \<turnstile> P \<Longrightarrow> un T \<Longrightarrow> \<Gamma>(x \<mapsto> T) \<turnstile>  P\<close>
  sorry

lemma
  assumes \<open>\<Gamma> \<turnstile> P\<close> and \<open>x \<notin> free_names P\<close>
  shows \<open>\<forall>T. (x, TOut T) \<notin> Map.graph \<Gamma>\<close>
    and \<open>\<forall>T. (x, TIn T) \<notin> Map.graph \<Gamma>\<close>
    and \<open>\<Gamma> = \<Gamma>'(x \<mapsto> T) \<Longrightarrow> \<Gamma>' \<turnstile> P\<close>
  sorry

lemma \<open>\<Gamma> \<turnstile> P \<Longrightarrow> P \<^bold>\<equiv> Q \<Longrightarrow> \<Gamma> \<turnstile> Q\<close>
  sorry

lemma \<open>\<Gamma>\<^sub>1 \<turnstile>\<^sub>v v : T \<Longrightarrow> \<Gamma>\<^sub>2(x \<mapsto> T) \<turnstile> P \<Longrightarrow> \<Gamma>\<^sub>1 \<circle> \<Gamma>\<^sub>2 = \<Gamma> \<Longrightarrow> \<Gamma> \<turnstile> (open_var v P)\<close>
  sorry

theorem subject_reduction: \<open>\<Gamma> \<turnstile> P \<Longrightarrow> P \<longlongrightarrow> Q \<Longrightarrow> \<Gamma> \<turnstile> Q\<close>
  sorry

theorem type_safety: \<open>Map.empty \<turnstile> P \<Longrightarrow> wf_process P\<close>
  sorry

corollary \<open>Map.empty \<turnstile> P \<Longrightarrow> P \<longlongrightarrow> Q \<Longrightarrow> wf_process Q\<close>
  using subject_reduction type_safety by blast

end