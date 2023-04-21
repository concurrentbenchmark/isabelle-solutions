theory Scope_Extrusion
  imports Main
begin

section \<open>Syntax\<close>

type_synonym atom = string
type_synonym index = nat

datatype name =
  Free atom (\<open>\<circ>' _\<close> [200] 990)
| Bound index (\<open>\<bullet>' _\<close> [200] 990)

datatype process =
  PInaction (\<open>\<zero>\<close>)
| POutput name name process (\<open>_\<^bold>!_._\<close> [130, 130, 130] 160)
| PInput name process (\<open>_\<^bold>?._\<close> [130,130] 160)  (* this binds a name *)
| PParallel process process (infix \<open>\<^bold>|\<close> 120)
| PRestrict process (\<open>'(\<nu>')' _\<close> [130] 160) (* this binds a name *)
| PChoice process process (infix \<open>\<^bold>+\<close> 120)

text \<open>Example processes\<close>
term \<open>\<circ>''a''\<^bold>!\<circ>''b''.P \<^bold>| Q\<close>
term \<open>(\<nu>) P \<^bold>| Q\<close>
term \<open>\<bullet>0\<^bold>?.P \<^bold>+ Q\<close> (* this is an invalid term: it contains an unguarded bound name *)

subsection \<open>Locally nameless machinery\<close>
subsubsection \<open>Opening\<close>
fun open_name_name where
  \<open>open_name_name _ _ (\<circ>n) = \<circ>n\<close>
| \<open>open_name_name k x (\<bullet>i) = (if i = k then \<circ>x else \<bullet>i)\<close>

fun open_name where
  \<open>open_name _ _ \<zero> = \<zero>\<close>
| \<open>open_name k x (a\<^bold>!b. P) = open_name_name k x a\<^bold>!open_name_name k x b.(open_name k x P)\<close>
| \<open>open_name k x (a\<^bold>?.P) = open_name_name k x a\<^bold>?.open_name (k + 1) x P\<close>
| \<open>open_name k x (P \<^bold>| Q) = open_name k x P \<^bold>| open_name k x Q\<close>
| \<open>open_name k x ((\<nu>)P) = (\<nu>) open_name (k + 1) x P\<close>
| \<open>open_name k x (P \<^bold>+ Q) = open_name k x P \<^bold>+ open_name k x Q\<close>

definition opening_name where
  \<open>opening_name x P \<equiv> open_name 0 x P\<close>

subsubsection \<open>Closing\<close>
fun close_name_name where
  \<open>close_name_name k x (\<circ>n) = (if x = n then \<bullet>k else \<circ>n)\<close>
| \<open>close_name_name _ _ (\<bullet>i) = \<bullet>i\<close>

fun close_name where
  \<open>close_name _ _ \<zero> = \<zero>\<close>
| \<open>close_name k x (a\<^bold>!b. P) = close_name_name k x a\<^bold>!close_name_name k x b.(close_name k x P)\<close>
| \<open>close_name k x (a\<^bold>?.P) = close_name_name k x a\<^bold>?.close_name (k + 1) x P\<close>
| \<open>close_name k x (P \<^bold>| Q) = close_name k x P \<^bold>| close_name k x Q\<close>
| \<open>close_name k x ((\<nu>)P) = (\<nu>) close_name (k + 1) x P\<close>
| \<open>close_name k x (P \<^bold>+ Q) = close_name k x P \<^bold>+ close_name k x Q\<close>

definition closing_name where
  \<open>closing_name x P \<equiv> close_name 0 x P\<close>

subsubsection \<open>Locally closed terms\<close>
inductive lc_name where
  LCFree: \<open>lc_name (\<circ>x)\<close>

inductive lc where
  LCInaction: \<open>lc \<zero>\<close>
| LCOutput:   \<open>\<lbrakk>lc_name x; lc_name y; lc P\<rbrakk> \<Longrightarrow> lc (x\<^bold>!y. P)\<close>
| LCInput:    \<open>\<lbrakk>lc_name x; \<exists>L. finite L \<and> (\<forall>y. y \<notin> L \<longrightarrow> lc (opening_name y P))\<rbrakk> \<Longrightarrow> lc (x\<^bold>?.P)\<close>
| LCParallel: \<open>\<lbrakk>lc P; lc Q\<rbrakk> \<Longrightarrow> lc (P \<^bold>| Q)\<close>
| LCRestrict: \<open>\<lbrakk>\<exists>L. finite L \<and> (\<forall>y. y \<notin> L \<longrightarrow> lc (opening_name y P))\<rbrakk> \<Longrightarrow> lc ((\<nu>)P)\<close>
| LCChoice:   \<open>\<lbrakk>lc P; lc Q\<rbrakk> \<Longrightarrow> lc (P \<^bold>+ Q)\<close>

definition body where
  \<open>body P \<equiv> \<exists>L. finite L \<and> (\<forall>x. x \<notin> L \<longrightarrow> lc (opening_name x P))\<close>

lemma lc_input_iff_body: \<open>lc (x\<^bold>?.P) \<longleftrightarrow> (body P \<and> lc_name x)\<close>
  unfolding body_def
proof (safe)
  assume *: \<open>lc (x\<^bold>?.P)\<close>
  then show \<open>\<exists>L. finite L \<and> (\<forall>x. x \<notin> L \<longrightarrow> lc (opening_name x P))\<close>
    using lc.cases by fastforce
next
  assume \<open>lc (x\<^bold>?.P)\<close>
  then show \<open>lc_name x\<close>
    using lc.cases by blast
next
  fix L
  assume \<open>lc_name x\<close> \<open>finite L\<close> \<open>\<forall>x. x \<notin> L \<longrightarrow> lc (opening_name x P)\<close> 
  then show \<open>lc (x\<^bold>?.P)\<close>
    using LCInput by blast
qed

lemma lc_restriction_iff_body: \<open>lc ((\<nu>)P) \<longleftrightarrow> body P\<close>
  unfolding body_def
proof
  assume *: \<open>lc ((\<nu>)P)\<close>
  then show \<open>\<exists>L. finite L \<and> (\<forall>x. x \<notin> L \<longrightarrow> lc (opening_name x P))\<close>
    using lc.cases by fastforce
next
  assume \<open>\<exists>L. finite L \<and> (\<forall>x. x \<notin> L \<longrightarrow> lc (opening_name x P))\<close>
  then show \<open>lc ((\<nu>)P)\<close>
    by (simp add: LCRestrict)
qed

lemma open_var_lc: \<open>body P \<Longrightarrow> lc (opening_name x P)\<close>
proof (unfold body_def)
  assume \<open>\<exists>L. finite L \<and> (\<forall>x. x \<notin> L \<longrightarrow> lc (opening_name x P))\<close>
  then obtain L where *: \<open>finite L\<close> \<open>\<forall>x. x \<notin> L \<longrightarrow> lc (opening_name x P)\<close>
    by blast
  then show \<open>lc (opening_name x P)\<close>
    sorry
qed

lemma close_var_lc: \<open>lc P \<Longrightarrow> body (closing_name x P)\<close>
  unfolding body_def
proof
  assume \<open>lc P\<close>
  then have \<open>(\<forall>y. y \<notin> {x} \<longrightarrow> lc (opening_name y (closing_name x P)))\<close>
  proof (induction P rule: lc.induct)
    case LCInaction
    then show ?case
      by (simp add: closing_name_def lc.LCInaction opening_name_def)
  next
    case (LCOutput x' y' P)
    fix z :: \<open>char list\<close>
    from \<open>lc_name x'\<close> have \<open>\<exists>xn. x' = Free xn\<close>
      using lc_name.simps by auto
    moreover from \<open>lc_name y'\<close> have \<open>\<exists>yn. y' = Free yn\<close>
      using lc_name.simps by auto
    ultimately show ?case
      unfolding opening_name_def closing_name_def
      by (smt (verit, ccfv_threshold) LCOutput.IH close_name.simps close_name_name.simps(1) closing_name_def lc.simps lc_name.intros open_name.simps open_name_name.simps opening_name_def)
  next
    case (LCInput P x')
    then show ?case
      sorry
  next
    case (LCParallel P Q)
    then show ?case sorry
  next
    case (LCRestrict P)
    then show ?case sorry
  next
    case (LCChoice P Q)
    then show ?case sorry
  qed
  then show \<open>finite {x} \<and> (\<forall>y. y \<notin> {x} \<longrightarrow> lc (opening_name y (closing_name x P)))\<close>
    by simp 
qed

subsubsection \<open>Free names\<close>
fun fn_names where
  \<open>fn_names (\<circ>n) = {n}\<close>
| \<open>fn_names (\<bullet>i) = {}\<close>

fun fn where
  \<open>fn \<zero> = {}\<close>
| \<open>fn (x\<^bold>!y. P) = fn_names x \<union> fn_names y \<union> fn P\<close>
| \<open>fn (x\<^bold>?.P) = fn_names x \<union> fn P\<close>
| \<open>fn (P \<^bold>| Q) = fn P \<union> fn Q\<close>
| \<open>fn ((\<nu>)P) = fn P\<close>
| \<open>fn (P \<^bold>+ Q) = fn P \<union> fn Q\<close>

definition fresh (infix \<open>\<sharp>\<close> 110) where
  \<open>n \<sharp> P \<equiv> n \<notin> fn P\<close>

definition closed where
  \<open>closed P \<equiv> fn P = {}\<close>

lemma open_var_fn: \<open>fn (opening_name x P) \<subseteq> fn P \<union> {x}\<close>
  unfolding opening_name_def
proof (induction P)
  case (POutput x1 x2 P)
  then show ?case sorry
next
  case (PInput x1 P)
  then show ?case sorry
next
  case (PRestrict P)
  then show ?case sorry
qed auto

lemma close_var_fn: \<open>fn (closing_name x P) = fn P - {x}\<close>
  unfolding closing_name_def
proof (induction P)
  case (POutput a b P)
  then show ?case sorry
next
  case (PInput x1 P)
  then show ?case sorry
next
  case (PRestrict P)
  then show ?case sorry
qed auto

subsubsection \<open>Substitution\<close>
fun subst_name where
  \<open>subst_name (\<circ>n) a b = (if b = n then a else \<circ>n)\<close>
| \<open>subst_name (\<bullet>i) _ _ = \<bullet>i\<close>

fun subst (\<open>_\<lbrace>' _'/' _\<rbrace>\<close> [200, 900, 900] 200) where
  \<open>\<zero>\<lbrace>a/b\<rbrace> = \<zero>\<close>
| \<open>(x\<^bold>!y. P)\<lbrace>a/b\<rbrace> = (subst_name x a b\<^bold>!subst_name y a b. P\<lbrace>a/b\<rbrace>)\<close>
| \<open>(x\<^bold>?.P)\<lbrace>a/b\<rbrace> = subst_name x a b\<^bold>?.P\<lbrace>a/b\<rbrace>\<close>
| \<open>(P \<^bold>| Q)\<lbrace>a/b\<rbrace> = (P\<lbrace>a/b\<rbrace>) \<^bold>| (Q\<lbrace>a/b\<rbrace>)\<close>
| \<open>((\<nu>)P)\<lbrace>a/b\<rbrace> = (\<nu>)(P\<lbrace>a/b\<rbrace>)\<close>
| \<open>(P \<^bold>+ Q)\<lbrace>a/b\<rbrace> = (P\<lbrace>a/b\<rbrace>) \<^bold>+ (Q\<lbrace>a/b\<rbrace>)\<close>

lemma subst_lc: \<open>\<lbrakk>lc P; lc_name y\<rbrakk> \<Longrightarrow> lc (P\<lbrace>y/x\<rbrace>)\<close>
proof (induction P rule: lc.induct)
  case (LCOutput x y P)
  then show ?case sorry
next
  case (LCInput P x)
  then show ?case sorry
next
  case (LCRestrict P)
  then show ?case sorry
qed (simp_all add: lc.intros)

lemma subst_body: \<open>\<lbrakk>body P; lc_name y\<rbrakk> \<Longrightarrow> body (P\<lbrace>y/x\<rbrace>)\<close>
proof (induction P)
  case PInaction
  then show ?case
    by simp
qed (metis lc_input_iff_body subst.simps(3) subst_lc)+

lemma subst_open_var: \<open>\<lbrakk>x \<noteq> y; lc_name z\<rbrakk> \<Longrightarrow> (opening_name y P)\<lbrace>z/x\<rbrace> = opening_name y (P\<lbrace>z/x\<rbrace>)\<close>
  unfolding opening_name_def
proof (induction P)
  case (POutput x1 x2 P)
  then show ?case sorry
next
  case (PInput x1 P)
  then show ?case sorry
next
  case (PRestrict P)
  then show ?case sorry
qed auto

lemma subst_close_var: \<open>\<lbrakk>x \<noteq> y; y \<noteq> z\<rbrakk> \<Longrightarrow> (closing_name y P)\<lbrace>\<circ>z/x\<rbrace> = closing_name y (P\<lbrace>\<circ>z/x\<rbrace>)\<close>
  sorry

lemma subst_fresh: \<open>x \<sharp> P \<Longrightarrow> P\<lbrace>y/x\<rbrace> = P\<close>
  unfolding fresh_def
proof (induction P)
  case (POutput x1 x2 P)
  moreover from POutput have \<open>x \<notin> fn_names x1\<close> \<open>x \<notin> fn_names x2\<close>
    by simp+
  then have \<open>subst_name x1 y x = x1\<close> \<open>subst_name x2 y x = x2\<close>
    by (metis fn_names.elims insertCI subst_name.simps)+
  ultimately show ?case
    by simp
next
  case (PInput x1 P)
  then show ?case
    by (metis UnI1 UnI2 fn.simps(3) fn_names.elims insertCI subst.simps(3) subst_name.simps)
qed simp_all

subsection \<open>Examples\<close>
lemma \<open>lc (\<circ>''a''\<^bold>!\<circ>''b''.\<zero> \<^bold>| \<zero>)\<close>
  using LCInaction LCOutput LCParallel lc_name.intros by auto

lemma \<open>lc ((\<nu>) (\<zero> \<^bold>| \<bullet>0\<^bold>!\<circ>''a''.\<zero>))\<close>
proof (rule LCRestrict, rule exI)
  show \<open>finite {''a''} \<and> (\<forall>y. y \<notin> {''a''} \<longrightarrow> lc (opening_name y (\<zero> \<^bold>| \<bullet>0\<^bold>!\<circ>''a''.\<zero>)))\<close>
  proof
    show \<open>finite {''a''}\<close> by simp
  next
    show \<open>\<forall>y. y \<notin> {''a''} \<longrightarrow> lc (opening_name y (\<zero> \<^bold>| \<bullet>0\<^bold>!\<circ>''a''.\<zero>))\<close>
    proof (rule allI, rule impI)
      fix y
      assume \<open>y \<notin> {''a''}\<close>
      have \<open>lc (\<zero> \<^bold>| \<circ>y\<^bold>!\<circ>''a''.\<zero>)\<close>
      proof
        show \<open>lc \<zero>\<close> ..
      next
        show \<open>lc (\<circ>y\<^bold>!\<circ>''a''.\<zero>)\<close>
        proof
          show \<open>lc_name (\<circ>y)\<close> ..
        next
          show \<open>lc_name (\<circ>''a'')\<close> ..
        next
          show \<open>lc \<zero>\<close> ..
        qed
      qed
      then show \<open>lc (opening_name y (\<zero> \<^bold>| \<bullet>0\<^bold>!\<circ>''a''.\<zero>))\<close>
        unfolding opening_name_def by simp
    qed
  qed
qed

lemma \<open>\<not> lc (\<bullet>0\<^bold>?.P \<^bold>+ Q)\<close>
proof
  assume \<open>lc (\<bullet>0\<^bold>?.P \<^bold>+ Q)\<close>
  then show False
  proof (rule lc.cases; auto)
    assume \<open>lc (\<bullet>0\<^bold>?.P)\<close>
    then show False
    proof (rule lc.cases; auto)
      assume \<open>lc_name (\<bullet>0)\<close>
      then show False
        using lc_name.cases by auto
    qed
  qed
qed

section \<open>Semantics\<close>

subsection \<open>Actions\<close>
datatype action =
  AFreeOut atom atom (\<open>_\<^bold>!_\<close> [300,300] 400)
| ABoundOut atom atom (\<open>_\<^bold>!'(_')\<close> [300,300] 400)
| AIn atom atom (\<open>_\<^bold>?_\<close> [300,300] 400)
| AInternal (\<open>\<tau>\<close>)

fun names where
  \<open>names (x\<^bold>!y) = {x,y}\<close>
| \<open>names (x\<^bold>!(y)) = {x,y}\<close>
| \<open>names (x\<^bold>?y) = {x,y}\<close>
| \<open>names \<tau> = {}\<close>

inductive transition :: \<open>process \<Rightarrow> action \<Rightarrow> process \<Rightarrow> bool\<close> (\<open>_ \<midarrow>_\<rightarrow> _\<close> [100,400,100] 800) where
  TOut: \<open>lc P \<Longrightarrow> (\<circ>x\<^bold>!\<circ>y. P) \<midarrow>x\<^bold>!y\<rightarrow> P\<close>
| TIn:  \<open>body P \<Longrightarrow> (\<circ>x\<^bold>?.P) \<midarrow>x\<^bold>?y\<rightarrow> opening_name y P\<close>
| TSumL: \<open>lc P \<Longrightarrow> lc Q \<Longrightarrow> P \<midarrow>\<alpha>\<rightarrow> P' \<Longrightarrow> (P \<^bold>+ Q) \<midarrow>\<alpha>\<rightarrow> P'\<close>
| TSumR: \<open>lc Q \<Longrightarrow> lc P \<Longrightarrow> P \<midarrow>\<alpha>\<rightarrow> P' \<Longrightarrow> (Q \<^bold>+ P) \<midarrow>\<alpha>\<rightarrow> P'\<close>
| TParL: \<open>\<lbrakk>lc P; lc Q; names \<alpha> \<inter> fn Q = {}; P \<midarrow>\<alpha>\<rightarrow> P'\<rbrakk> \<Longrightarrow> (P \<^bold>| Q) \<midarrow>\<alpha>\<rightarrow> (P' \<^bold>| Q)\<close>
| TParR: \<open>\<lbrakk>lc P; lc Q; names \<alpha> \<inter> fn P = {}; Q \<midarrow>\<alpha>\<rightarrow> Q'\<rbrakk> \<Longrightarrow> (P \<^bold>| Q) \<midarrow>\<alpha>\<rightarrow> (P \<^bold>| Q')\<close>
| TCommL: \<open>\<lbrakk>P \<midarrow>x\<^bold>!y\<rightarrow> P'; Q \<midarrow>x\<^bold>?y\<rightarrow> Q'\<rbrakk> \<Longrightarrow> (P \<^bold>| Q) \<midarrow>\<tau>\<rightarrow> (P' \<^bold>| Q')\<close>
| TCommR: \<open>\<lbrakk>P \<midarrow>x\<^bold>?y\<rightarrow> P'; Q \<midarrow>x\<^bold>!y\<rightarrow> Q'\<rbrakk> \<Longrightarrow> (P \<^bold>| Q) \<midarrow>\<tau>\<rightarrow> (P' \<^bold>| Q')\<close>
| TCloseL: \<open>\<lbrakk>P \<midarrow>x\<^bold>!(z)\<rightarrow> P'; Q \<midarrow>x\<^bold>?z\<rightarrow> Q'; z \<sharp> Q\<rbrakk> \<Longrightarrow> (P \<^bold>| Q) \<midarrow>\<tau>\<rightarrow> ((\<nu>) closing_name z (P' \<^bold>| Q'))\<close>
| TCloseR: \<open>\<lbrakk>P \<midarrow>x\<^bold>?z\<rightarrow> P'; Q \<midarrow>x\<^bold>!(z)\<rightarrow> Q'; z \<sharp> P\<rbrakk> \<Longrightarrow> (P \<^bold>| Q) \<midarrow>\<tau>\<rightarrow> ((\<nu>) closing_name z (P' \<^bold>| Q'))\<close>
| TOpen: \<open>\<lbrakk>opening_name z P \<midarrow>x\<^bold>!z\<rightarrow> opening_name z P'; z \<noteq> x\<rbrakk> \<Longrightarrow> ((\<nu>) P) \<midarrow>x\<^bold>!(z)\<rightarrow> opening_name z P'\<close>
| TRes: \<open>lc P \<Longrightarrow> P \<midarrow>\<alpha>\<rightarrow> P' \<Longrightarrow> ((\<nu>) P) \<midarrow>\<alpha>\<rightarrow> (\<nu>) P'\<close>

lemma regularity: \<open>P \<midarrow>\<alpha>\<rightarrow> P' \<Longrightarrow> lc P \<and> lc P'\<close>
  sorry

subsection \<open>Examples\<close>

lemma \<open>(((\<nu>) (\<circ>''x''\<^bold>!\<bullet>0.\<bullet>0\<^bold>!\<circ>''a''.\<bullet>0\<^bold>!\<circ>''b''.\<zero>)) \<^bold>| \<circ>''x''\<^bold>?.(\<bullet>0\<^bold>?.\<bullet>1\<^bold>?.\<bullet>1\<^bold>!\<bullet>0.\<zero> \<^bold>| \<circ>''z''\<^bold>?.\<zero>))
              \<midarrow>\<tau>\<rightarrow> ((\<nu>) (\<bullet>0\<^bold>!\<circ>''a''.\<bullet>0\<^bold>!\<circ>''b''.\<zero> \<^bold>| (\<bullet>0\<^bold>?.\<bullet>1\<^bold>?.\<bullet>1\<^bold>!\<bullet>0.\<zero> \<^bold>| \<circ>''z''\<^bold>?.\<zero>)))\<close>
proof -
  have \<open>((\<nu>) (\<circ>''x''\<^bold>!\<bullet>0.\<bullet>0\<^bold>!\<circ>''a''.\<bullet>0\<^bold>!\<circ>''b''.\<zero>)) \<midarrow>''x''\<^bold>!(''s'')\<rightarrow> opening_name ''s'' (\<bullet>0\<^bold>!\<circ>''a''.\<bullet>0\<^bold>!\<circ>''b''.\<zero>)\<close>
  proof (rule TOpen)
    have \<open>\<circ>''x''\<^bold>!\<circ>''s''.\<circ>''s''\<^bold>!\<circ>''a''.\<circ>''s''\<^bold>!\<circ>''b''.\<zero> \<midarrow>''x''\<^bold>!''s''\<rightarrow> \<circ>''s''\<^bold>!\<circ>''a''. \<circ>''s''\<^bold>!\<circ>''b''.\<zero>\<close>
      by (rule TOut) (simp add: LCInaction LCOutput lc_name.intros)
    then show \<open>opening_name ''s'' (\<circ>''x''\<^bold>!\<bullet>0.\<bullet>0\<^bold>!\<circ>''a''.\<bullet>0\<^bold>!\<circ>''b''.\<zero>) \<midarrow>''x''\<^bold>!''s''\<rightarrow> opening_name ''s'' (\<bullet>0\<^bold>!\<circ>''a''.\<bullet>0\<^bold>!\<circ>''b''.\<zero>)\<close>
      unfolding opening_name_def by simp
  qed (simp)
  then have \<open>((\<nu>) (\<circ>''x''\<^bold>!\<bullet>0.\<bullet>0\<^bold>!\<circ>''a''.\<bullet>0\<^bold>!\<circ>''b''.\<zero>)) \<midarrow>''x''\<^bold>!(''s'')\<rightarrow> \<circ>''s''\<^bold>!\<circ>''a''. \<circ>''s''\<^bold>!\<circ>''b''.\<zero>\<close>
    unfolding opening_name_def by simp
  moreover have \<open>\<circ>''x''\<^bold>?.(\<bullet>0\<^bold>?.\<bullet>1\<^bold>?.\<bullet>1\<^bold>!\<bullet>0.\<zero> \<^bold>| \<circ>''z''\<^bold>?.\<zero>) \<midarrow>''x''\<^bold>?''s''\<rightarrow> opening_name ''s'' (\<bullet>0\<^bold>?.\<bullet>1\<^bold>?.\<bullet>1\<^bold>!\<bullet>0.\<zero> \<^bold>| \<circ>''z''\<^bold>?.\<zero>)\<close>
  proof (rule TIn)
    show \<open>body (\<bullet>0\<^bold>?.\<bullet>1\<^bold>?.\<bullet>1\<^bold>!\<bullet>0.\<zero> \<^bold>| \<circ>''z''\<^bold>?.\<zero>)\<close>
      unfolding body_def
    proof (rule exI, rule conjI)
      show \<open>finite {}\<close> by simp
    next
      show \<open>\<forall>x. x \<notin> {} \<longrightarrow> lc (opening_name x (\<bullet>0\<^bold>?.\<bullet>1\<^bold>?.\<bullet>1\<^bold>!\<bullet>0.\<zero> \<^bold>| \<circ>''z''\<^bold>?.\<zero>))\<close>
      proof
        fix x
        show \<open>x \<notin> {} \<longrightarrow> lc (opening_name x (\<bullet>0\<^bold>?.\<bullet>1\<^bold>?.\<bullet>1\<^bold>!\<bullet>0.\<zero> \<^bold>| \<circ>''z''\<^bold>?.\<zero>))\<close>
        proof
          assume \<open>x \<notin> {}\<close>
          have \<open>lc (\<circ>x\<^bold>?.\<circ>x\<^bold>?.\<bullet>1\<^bold>!\<bullet>0.\<zero> \<^bold>| \<circ>''z''\<^bold>?.\<zero>)\<close>
          proof (rule LCParallel)
            show \<open>lc (\<circ>x\<^bold>?.\<circ>x\<^bold>?.\<bullet>1\<^bold>!\<bullet>0.\<zero>)\<close>
            proof (rule LCInput)
              show \<open>lc_name (\<circ>x)\<close> by (rule LCFree)
            next
              show \<open>\<exists>L. finite L \<and> (\<forall>y. y \<notin> L \<longrightarrow> lc (opening_name y (\<circ>x\<^bold>?.\<bullet>1\<^bold>!\<bullet>0.\<zero>)))\<close>
              proof (rule exI, rule conjI)
                show \<open>finite {}\<close> by simp
              next
                show \<open>\<forall>y. y \<notin> {} \<longrightarrow> lc (opening_name y (\<circ>x\<^bold>?.\<bullet>1\<^bold>!\<bullet>0.\<zero>)) \<close>
                proof (rule allI, rule impI)
                  fix y :: atom
                  assume \<open>y \<notin> {}\<close>
                  have \<open>lc (\<circ>x\<^bold>?.\<circ>y\<^bold>!\<bullet>0.\<zero>)\<close>
                  proof (rule LCInput)
                    show \<open>lc_name (\<circ>x)\<close> by (rule LCFree)
                  next
                    show \<open>\<exists>L. finite L \<and> (\<forall>ya. ya \<notin> L \<longrightarrow> lc (opening_name ya (\<circ>y\<^bold>!\<bullet>0.\<zero>)))\<close>
                    proof (rule exI, rule conjI)
                      show \<open>finite {}\<close> by simp
                    next
                      show \<open>\<forall>w. w \<notin> {} \<longrightarrow> lc (opening_name w (\<circ>y\<^bold>!\<bullet>0.\<zero>))\<close>
                      proof (rule allI, rule impI)
                        fix w :: atom
                        assume \<open>w \<notin> {}\<close>
                        have \<open>lc (\<circ>y\<^bold>!\<circ>w.\<zero>)\<close>
                          by (simp add: LCInaction LCOutput lc_name.intros)
                        then show \<open>lc (opening_name w (\<circ>y\<^bold>!\<bullet>0.\<zero>))\<close>
                          unfolding opening_name_def by simp
                      qed
                    qed
                  qed
                  then show \<open>lc (opening_name y (\<circ>x\<^bold>?.\<bullet>1\<^bold>!\<bullet>0.\<zero>))\<close>
                    unfolding opening_name_def by simp
                qed
              qed
            qed
          next
            show \<open>lc (\<circ>''z''\<^bold>?.\<zero>)\<close>
              by (metis LCInaction LCInput infinite_imp_nonempty lc_name.intros open_name.simps(1) opening_name_def)
          qed
          then show \<open>lc (opening_name x (\<bullet>0\<^bold>?.\<bullet>1\<^bold>?.\<bullet>1\<^bold>!\<bullet>0.\<zero> \<^bold>| \<circ>''z''\<^bold>?.\<zero>))\<close>
            unfolding opening_name_def by simp
        qed
      qed 
    qed
  qed
  then have \<open>\<circ>''x''\<^bold>?.(\<bullet>0\<^bold>?.\<bullet>1\<^bold>?.\<bullet>1\<^bold>!\<bullet>0.\<zero> \<^bold>| \<circ>''z''\<^bold>?.\<zero>) \<midarrow>''x''\<^bold>?''s''\<rightarrow> (\<circ>''s''\<^bold>?.\<circ>''s''\<^bold>?.\<bullet>1\<^bold>!\<bullet>0.\<zero> \<^bold>| \<circ>''z''\<^bold>?.\<zero>)\<close>
    unfolding opening_name_def by simp
  ultimately have \<open>(\<nu>)\<circ>''x''\<^bold>!\<bullet>0.\<bullet>0\<^bold>!\<circ>''a''.\<bullet>0\<^bold>!\<circ>''b''.\<zero> \<^bold>|
    \<circ>''x''\<^bold>?.(\<bullet>0\<^bold>?.\<bullet>1\<^bold>?.\<bullet>1\<^bold>!\<bullet>0.\<zero> \<^bold>|
              \<circ>''z''\<^bold>?.\<zero>) \<midarrow>\<tau>\<rightarrow> (\<nu>) (closing_name ''s'' (\<bullet>0\<^bold>!\<circ>''a''.\<bullet>0\<^bold>!\<circ>''b''.\<zero> \<^bold>| (\<bullet>0\<^bold>?.\<bullet>1\<^bold>?.\<bullet>1\<^bold>!\<bullet>0.\<zero> \<^bold>| \<circ>''z''\<^bold>?.\<zero>)))\<close>
    sorry
  then show \<open>(\<nu>)\<circ>''x''\<^bold>!\<bullet>0.\<bullet>0\<^bold>!\<circ>''a''.\<bullet>0\<^bold>!\<circ>''b''.\<zero> \<^bold>|
    \<circ>''x''\<^bold>?.(\<bullet>0\<^bold>?.\<bullet>1\<^bold>?.\<bullet>1\<^bold>!\<bullet>0.\<zero> \<^bold>|
              \<circ>''z''\<^bold>?.\<zero>) \<midarrow>\<tau>\<rightarrow> (\<nu>) (\<bullet>0\<^bold>!\<circ>''a''.\<bullet>0\<^bold>!\<circ>''b''.\<zero> \<^bold>| (\<bullet>0\<^bold>?.\<bullet>1\<^bold>?.\<bullet>1\<^bold>!\<bullet>0.\<zero> \<^bold>| \<circ>''z''\<^bold>?.\<zero>))\<close>
    unfolding closing_name_def by simp
qed

section \<open>Bisimulation\<close>

subsection \<open>Observability\<close>

datatype observation =
  ObsIn atom (\<open>_\<^bold>\<questiondown>\<close>)
| ObsOut atom (\<open>_\<^bold>\<exclamdown>\<close>)

inductive observable (\<open>_\<down>\<^bsub>_\<^esub>\<close> [30,30] 30) where
  OIn: \<open>\<exists>P' y. P \<midarrow>x\<^bold>?y\<rightarrow> P' \<Longrightarrow> P\<down>\<^bsub>x\<^bold>\<questiondown>\<^esub>\<close>
| OOutFree: \<open>\<exists>P' y. P \<midarrow>x\<^bold>!y\<rightarrow> P' \<Longrightarrow> P\<down>\<^bsub>x\<^bold>\<exclamdown>\<^esub>\<close>
| OOutBound: \<open>\<exists>P' z. P \<midarrow>x\<^bold>!(z)\<rightarrow> P' \<Longrightarrow> P\<down>\<^bsub>x\<^bold>\<exclamdown>\<^esub>\<close>

subsection \<open>Strong barbed bisimulation\<close>

inductive bisimilar (infix \<open>\<sim>\<close> 200) where
\<open>\<lbrakk>
  P\<down>\<^bsub>\<mu>\<^esub> \<longrightarrow> Q\<down>\<^bsub>\<mu>\<^esub>; P \<midarrow>\<tau>\<rightarrow> P' \<longrightarrow> (\<exists>Q'. Q \<midarrow>\<tau>\<rightarrow> Q' \<and> P' \<sim> Q');
  Q\<down>\<^bsub>\<mu>\<^esub> \<longrightarrow> P\<down>\<^bsub>\<mu>\<^esub>; Q \<midarrow>\<tau>\<rightarrow> Q' \<longrightarrow> (\<exists>P'. P \<midarrow>\<tau>\<rightarrow> P' \<and> P' \<sim> Q')\<rbrakk>
  \<Longrightarrow> P \<sim> Q\<close>

section \<open>Bisimulation is an equivalence relation\<close>

theorem \<open>equivp (\<sim>)\<close>
  sorry

end