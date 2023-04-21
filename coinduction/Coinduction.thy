theory Coinduction
  imports Main
begin

section \<open>Syntax\<close>

type_synonym name = string

datatype process =
  Inaction (\<open>\<zero>\<close>)
  | Out name process (\<open>_\<^bold>!._\<close> [50, 60] 200)
  | In name process (\<open>_\<^bold>?._\<close> [50, 60] 200)
  | Composition process process (\<open>_\<^bold>|_\<close> [50, 50] 300)
  | Replicate process (\<open>\<^bold>!_\<close> [50] 100)

primrec names where
  \<open>names Inaction = {}\<close>
| \<open>names (Out x P) = {x} \<union> names P\<close>
| \<open>names (In x P) = {x} \<union> names P\<close>
| \<open>names (Composition P Q) = names P \<union> names Q\<close>
| \<open>names (Replicate P) = names P\<close>

section \<open>Semantics\<close>

datatype actions =
  AOut name (\<open>_\<^bold>!\<close> 100)
  | AIn name (\<open>_\<^bold>?\<close> 100)
  | ATau (\<open>\<tau>\<close>)

inductive transition (\<open>_\<midarrow>_\<rightarrow>_\<close> [20, 20, 20] 30) where
  TOut[intro]: \<open>x\<^bold>!.P \<midarrow>x\<^bold>!\<rightarrow> P\<close>
| TIn[intro]: \<open>x\<^bold>?.P \<midarrow>x\<^bold>?\<rightarrow> P\<close>
| TParL[intro]: \<open>P \<midarrow>\<alpha>\<rightarrow> P' \<Longrightarrow> P \<^bold>| Q \<midarrow>\<alpha>\<rightarrow> P' \<^bold>| Q\<close>
| TParR[intro]: \<open>Q \<midarrow>\<alpha>\<rightarrow> Q' \<Longrightarrow> P \<^bold>| Q \<midarrow>\<alpha>\<rightarrow> P \<^bold>| Q'\<close>
| TCommL[intro]: \<open>P \<midarrow>x\<^bold>!\<rightarrow> P' \<Longrightarrow> Q \<midarrow>x\<^bold>?\<rightarrow> Q' \<Longrightarrow> P \<^bold>| Q \<midarrow>\<tau>\<rightarrow> P' \<^bold>| Q'\<close>
| TCommR[intro]: \<open>P \<midarrow>x\<^bold>?\<rightarrow> P' \<Longrightarrow> Q \<midarrow>x\<^bold>!\<rightarrow> Q' \<Longrightarrow> P \<^bold>| Q \<midarrow>\<tau>\<rightarrow> P' \<^bold>| Q'\<close>
| TRep[intro]: \<open>P \<midarrow>\<alpha>\<rightarrow> P' \<Longrightarrow> \<^bold>!P \<midarrow>\<alpha>\<rightarrow> P' \<^bold>| \<^bold>!P\<close>

lemma inaction_stuck [simp]: \<open>\<nexists>P. (\<zero> \<midarrow>\<alpha>\<rightarrow> P)\<close>
proof
  assume \<open>\<exists>P. \<zero> \<midarrow>\<alpha>\<rightarrow> P\<close>
  then obtain P where \<open>\<zero> \<midarrow>\<alpha>\<rightarrow> P\<close> ..
  then show False
    using transition.simps by blast
qed

lemma out_no_tau [simp]: \<open>\<nexists>P Q. x\<^bold>!.P \<midarrow>\<tau>\<rightarrow> Q\<close>
proof
  assume \<open>\<exists>P Q. x\<^bold>!.P \<midarrow>\<tau>\<rightarrow> Q\<close>
  then obtain P Q where \<open>x\<^bold>!.P \<midarrow>\<tau>\<rightarrow> Q\<close> by blast
  then show False
    by cases
qed

lemma in_no_tau [simp]: \<open>\<nexists>P Q. x\<^bold>?.P \<midarrow>\<tau>\<rightarrow> Q\<close>
proof
  assume \<open>\<exists>P Q. x\<^bold>?.P \<midarrow>\<tau>\<rightarrow> Q\<close>
  then obtain P Q where \<open>x\<^bold>?.P \<midarrow>\<tau>\<rightarrow> Q\<close> by blast
  then show False
    by cases
qed

lemma out_elim [elim]:
  assumes \<open>x\<^bold>!.P \<midarrow>y\<^bold>!\<rightarrow> Q\<close>
  shows \<open>x = y\<close> and \<open>P = Q\<close>
proof -
  from assms show \<open>x = y\<close>
    by cases auto
next
  show \<open>P = Q\<close>
  proof (rule ccontr)
    assume \<open>P \<noteq> Q\<close>
    with assms show False
      by cases auto
  qed
qed

lemma in_elim [elim]:
  assumes \<open>x\<^bold>?.P \<midarrow>y\<^bold>?\<rightarrow> Q\<close>
  shows \<open>x = y\<close> and \<open>P = Q\<close>
proof -
  from assms show \<open>x = y\<close>
    by cases auto
next
  show \<open>P = Q\<close>
  proof (rule ccontr)
    assume \<open>P \<noteq> Q\<close>
    with assms show False
      by cases auto
  qed
qed

lemma CommL_deterministic [simp]: \<open>\<exists>! R. (x\<^bold>!.P) \<^bold>| (x\<^bold>?.Q) \<midarrow>\<tau>\<rightarrow> R\<close>
proof
  fix R
  assume \<open>(x\<^bold>!.P) \<^bold>| (x\<^bold>?.Q) \<midarrow>\<tau>\<rightarrow> R\<close>
  then show \<open>R = (P \<^bold>| Q)\<close>
  proof cases
    case (TParL P')
    with out_no_tau show ?thesis by blast
  next
    case (TParR Q')
    with in_no_tau show ?thesis by blast
  next
    case (TCommL x' P' Q')
    then have \<open>P = P'\<close> by auto
    moreover from TCommL have \<open>Q = Q'\<close> by auto
    ultimately show ?thesis using TCommL by simp
  next
    case (TCommR x P' Q')
    from this(2) have False
      by cases
    then show ?thesis ..
  qed
qed blast

lemma CommR_deterministic [simp]: \<open>\<exists>! R. (x\<^bold>?.P) \<^bold>| (x\<^bold>!.Q) \<midarrow>\<tau>\<rightarrow> R\<close>
proof
  fix R
  assume \<open>(x\<^bold>?.P) \<^bold>| (x\<^bold>!.Q) \<midarrow>\<tau>\<rightarrow> R\<close>
  then show \<open>R = (P \<^bold>| Q)\<close>
  proof cases
    case (TParL P')
    with in_no_tau show ?thesis by blast
  next
    case (TParR Q')
    with out_no_tau show ?thesis by blast
  next
    case (TCommL x' P' Q')
    from this(2) have False
      by cases
    then show ?thesis ..
  next
    case (TCommR x P' Q')
    then have \<open>P = P'\<close> by auto
    moreover from TCommR have \<open>Q = Q'\<close> by auto
    ultimately show ?thesis using TCommR by simp
  qed
qed blast

section \<open>Bisimilarity\<close>

datatype observables =
  OOut name
  | OIn name

inductive observable where
  ObsOut[intro]: \<open>\<exists>P'. P \<midarrow>AOut x\<rightarrow> P' \<Longrightarrow> observable P (OOut x)\<close>
| ObsIn[intro]: \<open>\<exists>P'. P \<midarrow>AIn x\<rightarrow> P' \<Longrightarrow> observable P (OIn x)\<close>

lemma obs_out_I [intro, simp]: \<open>observable (x\<^bold>!.P) (OOut x)\<close>
proof
  have \<open>x\<^bold>!.P \<midarrow>x\<^bold>!\<rightarrow> P\<close>
    by auto
  then show \<open>\<exists>P'. x\<^bold>!.P\<midarrow>x\<^bold>!\<rightarrow>P'\<close> ..
qed

lemma obs_in_I [intro, simp]: \<open>observable (x\<^bold>?.P) (OIn x)\<close>
proof
  have \<open>x\<^bold>?.P \<midarrow>x\<^bold>?\<rightarrow> P\<close>
    by auto
  then show \<open>\<exists>P'. x\<^bold>?.P\<midarrow>x\<^bold>?\<rightarrow>P'\<close> ..
qed

lemma obs_out_eq [simp]: \<open>y \<noteq> x \<Longrightarrow> \<not> observable (x\<^bold>!.P) (OOut y)\<close>
proof
  assume *: \<open>y \<noteq> x\<close>
  assume \<open>observable (x\<^bold>!.P) (OOut y)\<close>
  then show False
  proof (cases)
    case ObsOut
    then obtain P' where \<open>(x\<^bold>!.P) \<midarrow>y\<^bold>!\<rightarrow> P'\<close> ..
    then show False
      by cases (simp add: *)
  qed
qed

lemma obs_in_eq [simp]: \<open>y \<noteq> x \<Longrightarrow> \<not> observable (x\<^bold>?.P) (OIn y)\<close>
proof
  assume *: \<open>y \<noteq> x\<close>
  assume \<open>observable (x\<^bold>?.P) (OIn y)\<close>
  then show False
  proof (cases)
    case ObsIn
    then obtain P' where \<open>(x\<^bold>?.P) \<midarrow>y\<^bold>?\<rightarrow> P'\<close> ..
    then show False
      by cases (simp add: *)
  qed
qed

lemma out_not_obs_in [simp]: \<open>P = (x\<^bold>!.Q) \<Longrightarrow> \<not> observable P (OIn y)\<close>
proof
  assume *: \<open>P = (x\<^bold>!.Q)\<close>
  have \<open>\<forall>P'. \<not> (P \<midarrow>AIn y\<rightarrow> P')\<close>
  proof
    fix P'
    show \<open>\<not> (P \<midarrow>y\<^bold>?\<rightarrow> P')\<close>
      unfolding not_def *
      by (rule impI, induction P') (use transition.simps in blast)+
  qed
  moreover assume \<open>observable P (OIn y)\<close>
  ultimately show False
    using observable.simps by auto
qed

lemma in_not_obs_out [simp]: \<open>P = (x\<^bold>?.Q) \<Longrightarrow> \<not> observable P (OOut y)\<close>
proof
  assume *: \<open>P = (x\<^bold>?.Q)\<close>
  have \<open>\<forall>P'. \<not> (P \<midarrow>AOut y\<rightarrow> P')\<close>
  proof
    fix P'
    show \<open>\<not> (P \<midarrow>y\<^bold>!\<rightarrow> P')\<close>
      unfolding not_def *
      by (rule impI, induction P') (use transition.simps in blast)+
  qed
  moreover assume \<open>observable P (OOut y)\<close>
  ultimately show False
    using observable.simps by auto
qed

lemma zero_no_obs [simp]: \<open>\<not> (observable \<zero> \<mu>)\<close>
proof safe
  assume \<open>observable \<zero> \<mu>\<close>
  then show False
    by cases auto
qed

lemma par_add_obs [simp]:
  assumes *: \<open>observable (P \<^bold>| Q) \<mu>\<close>
  shows \<open>observable P \<mu> \<or> observable Q \<mu>\<close>
proof (cases \<open>observable P \<mu>\<close>)
  case False
  from * have \<open>observable Q \<mu>\<close>
  proof cases
    case (ObsOut x)
    with False have NP: \<open>\<nexists>P'. P \<midarrow>x\<^bold>!\<rightarrow> P'\<close> by fast
    from ObsOut obtain Q'' where PQ: \<open>P \<^bold>| Q \<midarrow>x\<^bold>!\<rightarrow> Q''\<close> by blast
    then have \<open>\<exists>Q'. Q \<midarrow>x\<^bold>!\<rightarrow> Q'\<close>
    proof cases
      case TParL
      with NP show ?thesis by blast
    next
      case TParR
      then show \<open>(\<exists>Q'. (Q\<midarrow>x\<^bold>!\<rightarrow>Q'))\<close>
        by blast
    qed
    then show ?thesis using ObsOut
      by blast
  next
    case (ObsIn x)
    with False have NP: \<open>\<nexists>P'. P \<midarrow>x\<^bold>?\<rightarrow> P'\<close> by fast
    from ObsIn obtain Q'' where PQ: \<open>P \<^bold>| Q \<midarrow>x\<^bold>?\<rightarrow> Q''\<close> by blast
    then have \<open>\<exists>Q'. Q \<midarrow>x\<^bold>?\<rightarrow> Q'\<close>
    proof cases
      case TParL
      with NP show ?thesis by blast
    next
      case TParR
      then show \<open>(\<exists>Q'. (Q\<midarrow>x\<^bold>?\<rightarrow>Q'))\<close>
        by blast
    qed
    then show ?thesis using ObsIn
      by blast
  qed
  then show ?thesis ..
qed simp

lemma rep_preserves_obs [simp]: \<open>observable (\<^bold>!P) \<mu> \<Longrightarrow> observable P \<mu>\<close>
proof (induction P arbitrary: \<mu>)
  case Inaction
  then show ?case
  proof cases
    case (ObsOut x)
    then obtain P' where \<open>\<^bold>!\<zero> \<midarrow>x\<^bold>!\<rightarrow> P'\<close> by blast
    then have False
    proof (cases)
      case (TRep Q)
      with zero_no_obs show ?thesis by fast
    qed
    then show ?thesis ..
  next
    case (ObsIn x)
    then obtain P' where \<open>\<^bold>!\<zero> \<midarrow>x\<^bold>?\<rightarrow> P'\<close> by blast
    then have False
    proof (cases)
      case (TRep Q)
      with zero_no_obs show ?thesis by fast
    qed
    then show ?thesis ..
  qed
next
  case (Out x P)
  from this(2) show ?case
  proof (cases)
    case (ObsOut x')
    then show ?thesis
    proof (cases \<open>x = x'\<close>)
      case False
      from ObsOut obtain P' where \<open>\<^bold>!(x\<^bold>!.P) \<midarrow>x'\<^bold>!\<rightarrow> P'\<close> by blast
      then have False
      proof cases
        case (TRep Q)
        with False show ?thesis
          by (simp add: out_elim)
      qed
      then show ?thesis ..
    qed simp
  next
    case (ObsIn x')
    then obtain P' where \<open>\<^bold>!(x\<^bold>!.P) \<midarrow>x'\<^bold>?\<rightarrow> P'\<close> by blast
    then have False
    proof cases
      case (TRep Q)
      then show ?thesis
        using out_not_obs_in by blast
    qed
    then show ?thesis ..
  qed
next
  case (In x P)
  from this(2) show ?case
  proof (cases)
    case (ObsIn x')
    then show ?thesis
    proof (cases \<open>x = x'\<close>)
      case False
      from ObsIn obtain P' where \<open>\<^bold>!(x\<^bold>?.P) \<midarrow>x'\<^bold>?\<rightarrow> P'\<close> by blast
      then have False
      proof cases
        case (TRep Q)
        with False show ?thesis
          by (simp add: in_elim)
      qed
      then show ?thesis ..
    qed simp
  next
    case (ObsOut x')
    then obtain P' where \<open>\<^bold>!(x\<^bold>?.P) \<midarrow>x'\<^bold>!\<rightarrow> P'\<close> by blast
    then have False
    proof cases
      case (TRep Q)
      then show ?thesis
        using in_not_obs_out by blast
    qed
    then show ?thesis ..
  qed
next
  case (Composition P Q)
  from this(3) show ?case
  proof cases
    case (ObsOut x)
    then obtain R where \<open>\<^bold>!(P \<^bold>| Q) \<midarrow>x\<^bold>!\<rightarrow> R\<close> by blast
    then show ?thesis
    proof (cases \<open>observable (\<^bold>!P) \<mu>\<close>)
      case True
      then show ?thesis
        using Composition.IH TParL observable.simps by metis
    next
      case False
      then have \<open>observable (\<^bold>!Q) \<mu>\<close>
        using ObsOut Composition.prems
        using Composition.IH
        sorry
      then show ?thesis
        using Composition.IH TParR observable.simps by metis
    qed
  next
    case (ObsIn x)
    then show ?thesis sorry
  qed
next
  case (Replicate P)
  from this(2) show ?case
  proof (cases)
    case (ObsOut x)
    then obtain R where \<open>\<^bold>!\<^bold>!P \<midarrow>x\<^bold>!\<rightarrow> R\<close> by blast
    then show ?thesis
    proof (cases)
      case (TRep P')
      then show ?thesis using ObsOut Replicate.IH sorry
    qed
  next
    case (ObsIn x)
    then show ?thesis sorry
  qed
qed

lemma obs_out_in_names: \<open>observable P (OOut x) \<Longrightarrow> x \<in> names P\<close>
proof (induction P)
  case (Out x' P)
  then show ?case
    by (cases \<open>x = x'\<close>) simp_all
next
  case (In x' P)
  then show ?case
    by (cases \<open>x = x'\<close>) simp_all
next
  case (Composition P Q)
  moreover from this consider \<open>observable P (OOut x)\<close> | \<open>observable Q (OOut x)\<close>
    using par_add_obs by blast
  ultimately show ?case
    by cases auto
next
  case (Replicate P)
  then show ?case sorry
qed simp

definition sim (\<open>_ \<sim>[_]\<leadsto> _\<close>) where
  \<open>P \<sim>[Rel]\<leadsto> Q \<equiv> (\<forall>\<mu>. observable P \<mu> \<longrightarrow> observable Q \<mu>) \<and>
                   (\<forall>P'. (P \<midarrow>\<tau>\<rightarrow> P') \<longrightarrow> (\<exists>Q'. (Q \<midarrow>\<tau>\<rightarrow> Q') \<and> (Q',P') \<in> Rel))\<close>

lemma simCases [consumes 1, case_names Obs Sim]:
  assumes \<open>\<And>\<mu>. observable P \<mu> \<Longrightarrow> observable Q \<mu>\<close>
    and \<open>\<And>P'. P \<midarrow>\<tau>\<rightarrow> P' \<Longrightarrow> \<exists>Q'. (Q \<midarrow>\<tau>\<rightarrow> Q') \<and> (Q',P') \<in> Rel\<close>
  shows \<open>P \<sim>[Rel]\<leadsto> Q\<close>
  unfolding sim_def by (simp add: assms)

lemma sim_E [elim]:
  assumes \<open>P \<sim>[Rel]\<leadsto> Q\<close>
  shows \<open>observable P \<mu> \<Longrightarrow> observable Q \<mu>\<close>
    and \<open>P \<midarrow>\<tau>\<rightarrow> P' \<Longrightarrow> \<exists>Q'. (Q \<midarrow>\<tau>\<rightarrow> Q') \<and> (Q',P') \<in> Rel\<close>
  using assms unfolding sim_def by auto

lemma sim_refl [simp]: \<open>Id \<subseteq> R \<Longrightarrow> P \<sim>[R]\<leadsto> P\<close>
  unfolding sim_def by auto

lemma sim_trans [simp]:
  assumes PQ: \<open>P \<sim>[X]\<leadsto> Q\<close>
      and QR: \<open>Q \<sim>[Y]\<leadsto> R\<close>
      and XYZ: \<open>Y O X \<subseteq> Z\<close>
    shows \<open>P \<sim>[Z]\<leadsto> R\<close>
proof (cases rule: simCases)
  fix \<mu>
  assume \<open>observable P \<mu>\<close>
  then have \<open>observable Q \<mu>\<close> using PQ by auto
  then show \<open>observable R \<mu>\<close> using QR by auto
next
  fix P'
  assume \<open>P\<midarrow>\<tau>\<rightarrow>P'\<close>
  then have \<open>\<exists>Q'. (Q\<midarrow>\<tau>\<rightarrow>Q') \<and> (Q', P') \<in> X\<close>
    using PQ by auto
  then obtain Q' where \<open>(Q\<midarrow>\<tau>\<rightarrow>Q')\<close> and X: \<open>(Q', P') \<in> X\<close> by blast
  then have \<open>\<exists>R'. (R\<midarrow>\<tau>\<rightarrow>R') \<and> (R', Q') \<in> Y\<close> using QR by auto
  then obtain R' where \<open>(R\<midarrow>\<tau>\<rightarrow>R')\<close> and Y: \<open>(R', Q') \<in> Y\<close> by blast
  moreover have \<open>(R', P') \<in> Z\<close> using X Y XYZ by auto
  ultimately show \<open>\<exists>R'. (R\<midarrow>\<tau>\<rightarrow>R') \<and> (R', P') \<in> Z\<close> by auto
qed

lemma monotonic:
  assumes "P \<sim>[A]\<leadsto> Q"
  and     "A \<subseteq> B"
  shows "P \<sim>[B]\<leadsto> Q"
  using assms by (fastforce simp add: sim_def)

lemma monoCoinduct: \<open>X \<le> Y \<Longrightarrow>
  (Q \<sim>[{(Q', P'). X Q' P'}]\<leadsto> P) \<longrightarrow> (Q \<sim>[{(Q', P'). Y Q' P'}]\<leadsto> P)\<close>
  by (meson Collect_case_prod_mono monotonic)

coinductive_set bisim where
  \<open>P \<sim>[bisim]\<leadsto> Q \<Longrightarrow> (Q,P) \<in> bisim \<Longrightarrow> (P,Q) \<in> bisim\<close>
monos monoCoinduct

abbreviation bisimulation (\<open>_ \<sim> _\<close> [60,60] 40) where
  \<open>P \<sim> Q \<equiv> (P,Q) \<in> bisim\<close>

lemma bisimCoinduct [case_names bisim bisym, consumes 1]:
  assumes pq: \<open>(P,Q) \<in> X\<close>
    and sim: \<open>\<And>R S. (R,S) \<in> X \<Longrightarrow> R \<sim>[X \<union> bisim]\<leadsto> S\<close>
    and sym: \<open>\<And>R S. (R,S) \<in> X \<Longrightarrow> (S,R) \<in> X\<close>
  shows \<open>P \<sim> Q\<close>
proof -
  have *: \<open>X \<union> bisim = {(P',Q'). (P',Q') \<in> X \<or> P' \<sim> Q'}\<close>
    by auto
  from pq show ?thesis
  proof (coinduct)
    case (bisim P Q)
    then show ?case
      using * sym sim by auto
  qed
qed

lemma bisim_E [elim]: \<open>P \<sim> Q \<Longrightarrow> P \<sim>[bisim]\<leadsto> Q\<close>
  by (auto intro: bisim.cases)

lemma bisim_I [intro]: \<open>P \<sim>[bisim]\<leadsto> Q \<Longrightarrow> Q \<sim> P \<Longrightarrow> P \<sim> Q\<close>
  by (rule bisim.intros)

lemma bisim_refl: \<open>reflp bisimulation\<close>
  unfolding reflp_def
proof
  fix P :: process
  have \<open>(P,P) \<in> Id\<close> ..
  then show \<open>P \<sim> P\<close>
    by (coinduct rule: bisimCoinduct) simp_all
qed

lemma bisim_sym: \<open>symp bisimulation\<close>
  by (auto dest: bisim.cases simp add: symp_def)

lemma bisim_trans: \<open>transp bisimulation\<close>
proof
  fix P Q R
  let ?BB = \<open>bisim O bisim\<close>
  assume \<open>P \<sim> Q\<close> \<open>Q \<sim> R\<close>
  then have \<open>(P,R) \<in> ?BB\<close> by blast
  then show \<open>P \<sim> R\<close>
  proof (coinduct rule: bisimCoinduct)
    case (bisim R S)
    then show ?case
      by (metis bisim_E prod.inject relcompE sim_trans sup_ge1)
  next
    case (bisym R S)
    then show ?case
      using bisim_sym sympE[of bisimulation] by auto
  qed
qed

theorem bisim_equiv: \<open>equivp bisimulation\<close>
  using bisim_refl bisim_sym bisim_trans equivpI by auto

subsection \<open>Examples\<close>

lemma \<open>x\<^bold>!.(y\<^bold>!.\<zero>) \<sim> x\<^bold>!.\<zero>\<close> (is \<open>?P \<sim> ?Q\<close>)
proof -
  let ?R = \<open>{(?P, ?Q), (?Q, ?P)}\<close>
  have \<open>(?P, ?Q) \<in> ?R\<close> by simp
  then show ?thesis
  proof (coinduct rule: bisimCoinduct)
    case (bisim R S)
    have \<open>R \<sim>[?R]\<leadsto> S\<close>
    proof (cases rule: simCases)
      fix \<mu>
      assume *: \<open>observable R \<mu>\<close>
      show \<open>observable S \<mu>\<close>
      proof (cases \<mu>)
        case (OOut x')
        then show ?thesis
          using bisim
        proof (cases R)
          case OR: (Out a R')
          then show ?thesis
            using bisim
          proof (cases S)
            case (Out b S')
            then have \<open>x' = x\<close>
              using OR OOut * obs_out_eq bisim by blast
            moreover have \<open>b = x\<close>
              using bisim Out by auto
            ultimately show ?thesis
              using Out OOut by simp
          qed simp_all
        qed simp_all
      next
        case (OIn x')
        then show ?thesis using bisim *
          by (cases R) simp_all
      qed
    next
      fix R'
      assume \<open>R \<midarrow>\<tau>\<rightarrow> R'\<close>
      then have \<open>False\<close>
        using bisim by cases blast+
      then show \<open>\<exists>S'. (S \<midarrow>\<tau>\<rightarrow> S') \<and> (S',R') \<in> ?R\<close> ..
    qed
    then show ?case
      using monotonic by blast
  qed auto
qed

lemma \<open>\<not> ((x\<^bold>!.(y\<^bold>!.\<zero>)) \<^bold>| (x\<^bold>?.\<zero>) \<sim> ((x\<^bold>!.\<zero>) \<^bold>| (x\<^bold>?.\<zero>)))\<close> (is \<open>\<not> (?P \<sim> ?Q)\<close>)
proof
  assume \<open>?P \<sim> ?Q\<close>
  then show False
  proof
    fix P Q
    assume \<open>Q \<sim> P\<close>
    let ?P' = \<open>(y\<^bold>!.\<zero>) \<^bold>| \<zero>\<close>
    assume \<open>?P = P\<close> \<open>?Q = Q\<close>
    moreover assume \<open>P \<sim>[bisim]\<leadsto> Q\<close>
    ultimately have \<open>?P \<sim>[bisim]\<leadsto> ?Q\<close>
      by simp
    then have \<open>\<And>P'. ?P \<midarrow>\<tau>\<rightarrow> P' \<Longrightarrow> \<exists>Q'. (?Q \<midarrow>\<tau>\<rightarrow> Q') \<and> (Q',P') \<in> bisim\<close>
      using sim_E by blast
    moreover have \<open>?P \<midarrow>\<tau>\<rightarrow> ?P'\<close>
      by auto
    ultimately have \<open>\<exists>Q'. (?Q \<midarrow>\<tau>\<rightarrow> Q') \<and> (Q',?P') \<in> bisim\<close>
      by auto
    then obtain Q' where \<open>(?Q \<midarrow>\<tau>\<rightarrow> Q')\<close> and *: \<open>(Q',?P') \<in> bisim\<close>
      by blast
    moreover from this have \<open>Q' = (\<zero> \<^bold>| \<zero>)\<close>
      using in_no_tau out_no_tau
    proof cases
      case (TCommL x' P' Q'')
      then show ?thesis
        using CommL_deterministic by blast
    next
      case (TCommR x' P' Q'')
      from this(2) have False
        by cases
      then show ?thesis ..
    qed fast+
    ultimately have \<open>\<zero> \<^bold>| \<zero> \<sim> ?P'\<close> by simp
    then show False
    proof
      fix R S
      assume \<open>(\<zero> \<^bold>| \<zero>) = R\<close> \<open>?P' = S\<close>
      moreover assume \<open>S \<sim> R\<close>
      ultimately have \<open>?P' \<sim>[bisim]\<leadsto> (\<zero> \<^bold>| \<zero>)\<close> by fast
      then have \<open>observable ?P' (OOut y) \<Longrightarrow> observable (\<zero> \<^bold>| \<zero>) (OOut y)\<close>
        using sim_E by blast
      then have \<open>observable (\<zero> \<^bold>| \<zero>) (OOut y)\<close> by blast
      then have \<open>observable \<zero> (OOut y)\<close>
        using par_add_obs by blast
      then show False by simp
    qed
  qed
qed

lemma \<open>\<^bold>!((x\<^bold>!.\<zero>) \<^bold>| (x\<^bold>?.\<zero>)) \<sim> (\<^bold>!(x\<^bold>!.\<zero>)) \<^bold>| (\<^bold>!(x\<^bold>?.\<zero>))\<close> (is \<open>?P \<sim> ?Q\<close>)
proof -
  let ?R = \<open>{(?P, ?Q), (?Q, ?P)}\<close>
  have \<open>(?P, ?Q) \<in> ?R\<close> by simp
  then show ?thesis
  proof (coinduct rule: bisimCoinduct)
    case (bisim R S)
    have \<open>R \<sim>[?R]\<leadsto> S\<close>
    proof (cases rule: simCases)
      fix \<mu>
      assume *: \<open>observable R \<mu>\<close>
      show \<open>observable S \<mu>\<close>
      proof (cases \<mu>)
        case (OOut x')
        then show ?thesis
          using bisim
        proof (cases R)
          case (Composition P Q)
          then have R: \<open>R = ((\<^bold>!(x\<^bold>!.\<zero>)) \<^bold>| (\<^bold>!(x\<^bold>?.\<zero>)))\<close>
            using bisim by simp
          then show ?thesis using bisim
          proof (cases S)
            case (Replicate P')
            then have \<open>S = \<^bold>!((x\<^bold>!.\<zero>)\<^bold>|(x\<^bold>?.\<zero>))\<close>
              using bisim by simp
            moreover from OOut * have \<open>x' = x\<close> sorry
            ultimately show ?thesis using * R OOut
              by blast
          qed simp_all
        next
          case (Replicate P')
          then show ?thesis sorry
        qed simp_all
      next
        case (OIn x')
        then show ?thesis using bisim * sorry
      qed
    next
      fix R'
      assume \<open>R \<midarrow>\<tau>\<rightarrow> R'\<close>
      then show \<open>\<exists>S'. (S \<midarrow>\<tau>\<rightarrow> S') \<and> (S',R') \<in> ?R\<close>
        using bisim sorry
    qed
    then show ?case
      using monotonic by blast
  qed fast
qed

section \<open>Reduction contexts\<close>

datatype ctx =
    CHole
  | CInaction
  | COut name ctx
  | CIn name ctx
  | CComposition ctx ctx
  | CReplicate ctx

primrec ctx_holes :: \<open>ctx \<Rightarrow> nat\<close> where
  \<open>ctx_holes CHole = 1\<close>
| \<open>ctx_holes CInaction = 0\<close>
| \<open>ctx_holes (COut _ P) = ctx_holes P\<close>
| \<open>ctx_holes (CIn _ P) = ctx_holes P\<close>
| \<open>ctx_holes (CComposition P Q) = ctx_holes P + ctx_holes Q\<close>
| \<open>ctx_holes (CReplicate P) = ctx_holes P\<close>

abbreviation \<open>wf_ctx C \<equiv> ctx_holes C = 1\<close>

primrec apply_ctx (\<open>_\<lbrakk>_\<rbrakk>\<close> [50, 50] 60) where
  \<open>apply_ctx CHole P = P\<close>
| \<open>apply_ctx CInaction P = Inaction\<close>
| \<open>apply_ctx (COut x C) P = Out x (apply_ctx C P)\<close>
| \<open>apply_ctx (CIn x C) P = In x (apply_ctx C P)\<close>
| \<open>apply_ctx (CComposition C1 C2) P = Composition (apply_ctx C1 P) (apply_ctx C2 P)\<close>
| \<open>apply_ctx (CReplicate C) P = Replicate (apply_ctx C P)\<close>

definition congruence where
  \<open>congruence S \<equiv> (\<forall>(P,Q) \<in> S. (\<forall>C. wf_ctx C \<longrightarrow> (C\<lbrakk>P\<rbrakk>, C\<lbrakk>Q\<rbrakk>) \<in> S))\<close>

section \<open>Strong barbed congruence\<close>

coinductive_set sbcong where
  \<open>(\<forall>C. wf_ctx C \<longrightarrow> C\<lbrakk>P\<rbrakk> \<sim> C\<lbrakk>Q\<rbrakk>) \<Longrightarrow> (P,Q) \<in> sbcong\<close>

abbreviation sbcongruence (\<open>_ \<simeq> _\<close> [50, 50] 70) where
  \<open>P \<simeq> Q \<equiv> (P,Q) \<in> sbcong\<close>

lemma sbcong_cong: \<open>congruence sbcong\<close>
  unfolding congruence_def
proof (safe)
  fix P Q C
  assume \<open>P \<simeq> Q\<close>
  assume \<open>wf_ctx C\<close>
  then show \<open>(C\<lbrakk>P\<rbrakk>) \<simeq> (C\<lbrakk>Q\<rbrakk>)\<close>
    sorry
qed

lemma sbcong_sym: \<open>symp sbcongruence\<close>
proof
  fix P Q
  assume \<open>P \<simeq> Q\<close>
  then have *: \<open>(\<forall>C. wf_ctx C \<longrightarrow> C\<lbrakk>P\<rbrakk> \<sim> C\<lbrakk>Q\<rbrakk>)\<close>
    by cases auto
  show \<open>Q \<simeq> P\<close>
  proof (coinduction)
    case sbcong
    have \<open>\<forall>C. wf_ctx C \<longrightarrow> C\<lbrakk>Q\<rbrakk> \<sim> C\<lbrakk>P\<rbrakk>\<close>
    proof (safe)
      fix C
      assume \<open>wf_ctx C\<close>
      then show \<open>C\<lbrakk>Q\<rbrakk> \<sim> C\<lbrakk>P\<rbrakk>\<close>
        using * bisim_sym bisim.cases by blast
    qed
    then show ?case
      by simp
  qed
qed

lemma sbcong_bisim: \<open>P \<simeq> Q \<Longrightarrow> P \<sim> Q\<close>
proof -
  assume \<open>(P,Q) \<in> sbcong\<close>
  then show \<open>P \<sim> Q\<close>
  proof (coinduct rule: bisimCoinduct)
    case (bisim R S)
    then show ?case sorry
  next
    case (bisym R S)
    then show ?case
      using sbcong_sym by (meson symp_def)
  qed
qed

lemma sbcong_largest: \<open>congruence S \<and> S \<subseteq> bisim \<Longrightarrow> S \<subseteq> sbcong\<close>
  oops

theorem challenge: \<open>P \<simeq> Q \<longleftrightarrow> (\<forall>R. (P \<^bold>| R) \<sim> (Q \<^bold>| R))\<close>
  oops

end