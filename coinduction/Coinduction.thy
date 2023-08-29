theory Coinduction
  imports Main
begin

section \<open>Syntax\<close>

type_synonym name = string

datatype process =
  Inaction (\<open>\<zero>\<close>)
  | Out name process (\<open>_\<^bold>!._\<close> [180, 150] 160)
  | In name process (\<open>_\<^bold>?._\<close> [180, 150] 160)
  | Composition process process (\<open>_\<^bold>|_\<close> [120,120] 140)
  | Replicate process (\<open>\<^bold>!_\<close> [150] 130)

primrec names where
  \<open>names Inaction = {}\<close>
| \<open>names (Out x P) = {x} \<union> names P\<close>
| \<open>names (In x P) = {x} \<union> names P\<close>
| \<open>names (Composition P Q) = names P \<union> names Q\<close>
| \<open>names (Replicate P) = names P\<close>

section \<open>Semantics\<close>

datatype actions =
  AOut name (\<open>_\<^bold>!\<close> 800)
  | AIn name (\<open>_\<^bold>?\<close> 800)
  | ATau (\<open>\<tau>\<close>)

inductive transition (\<open>_\<midarrow>_\<rightarrow>_\<close> [120, 500, 120] 115) where
  TOut[intro]: \<open>x\<^bold>!.P \<midarrow>x\<^bold>!\<rightarrow> P\<close>
| TIn[intro]: \<open>x\<^bold>?.P \<midarrow>x\<^bold>?\<rightarrow> P\<close>
| TParL[intro]: \<open>P \<midarrow>\<alpha>\<rightarrow> P' \<Longrightarrow> P \<^bold>| Q \<midarrow>\<alpha>\<rightarrow> P' \<^bold>| Q\<close>
| TParR[intro]: \<open>Q \<midarrow>\<alpha>\<rightarrow> Q' \<Longrightarrow> P \<^bold>| Q \<midarrow>\<alpha>\<rightarrow> P \<^bold>| Q'\<close>
| TCommL[intro]: \<open>P \<midarrow>x\<^bold>!\<rightarrow> P' \<Longrightarrow> Q \<midarrow>x\<^bold>?\<rightarrow> Q' \<Longrightarrow> P \<^bold>| Q \<midarrow>\<tau>\<rightarrow> P' \<^bold>| Q'\<close>
| TCommR[intro]: \<open>P \<midarrow>x\<^bold>?\<rightarrow> P' \<Longrightarrow> Q \<midarrow>x\<^bold>!\<rightarrow> Q' \<Longrightarrow> P \<^bold>| Q \<midarrow>\<tau>\<rightarrow> P' \<^bold>| Q'\<close>
| TRep[intro]: \<open>P \<midarrow>\<alpha>\<rightarrow> P' \<Longrightarrow> \<^bold>!P \<midarrow>\<alpha>\<rightarrow> P' \<^bold>| \<^bold>!P\<close>

lemma inaction_stuck [simp]: \<open>\<nexists>P. \<zero> \<midarrow>\<alpha>\<rightarrow> P\<close>
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

lemma CommL_deterministic [simp]: \<open>\<exists>! R. x\<^bold>!.P \<^bold>| x\<^bold>?.Q \<midarrow>\<tau>\<rightarrow> R\<close>
proof
  fix R
  assume \<open>x\<^bold>!.P \<^bold>| x\<^bold>?.Q \<midarrow>\<tau>\<rightarrow> R\<close>
  then show \<open>R = P \<^bold>| Q\<close>
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

lemma CommR_deterministic [simp]: \<open>\<exists>! R. x\<^bold>?.P \<^bold>| x\<^bold>!.Q \<midarrow>\<tau>\<rightarrow> R\<close>
proof
  fix R
  assume \<open>x\<^bold>?.P \<^bold>| x\<^bold>!.Q \<midarrow>\<tau>\<rightarrow> R\<close>
  then show \<open>R = P \<^bold>| Q\<close>
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
  ObsOut[intro]: \<open>\<exists>P'. P \<midarrow>x\<^bold>!\<rightarrow> P' \<Longrightarrow> observable P (OOut x)\<close>
| ObsIn[intro]: \<open>\<exists>P'. P \<midarrow>x\<^bold>?\<rightarrow> P' \<Longrightarrow> observable P (OIn x)\<close>

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
    then obtain P' where \<open>x\<^bold>!.P \<midarrow>y\<^bold>!\<rightarrow> P'\<close> ..
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
    then obtain P' where \<open>x\<^bold>?.P \<midarrow>y\<^bold>?\<rightarrow> P'\<close> ..
    then show False
      by cases (simp add: *)
  qed
qed

lemma out_not_obs_in [simp]: \<open>P = x\<^bold>!.Q \<Longrightarrow> \<not> observable P (OIn y)\<close>
proof
  assume *: \<open>P = x\<^bold>!.Q\<close>
  have \<open>\<forall>P'. \<not> (P \<midarrow>y\<^bold>?\<rightarrow> P')\<close>
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

lemma in_not_obs_out [simp]: \<open>P = x\<^bold>?.Q \<Longrightarrow> \<not> observable P (OOut y)\<close>
proof
  assume *: \<open>P = x\<^bold>?.Q\<close>
  have \<open>\<forall>P'. \<not> (P \<midarrow>y\<^bold>!\<rightarrow> P')\<close>
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
      then show \<open>\<exists>Q'. Q\<midarrow>x\<^bold>!\<rightarrow>Q'\<close>
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
      then show \<open>\<exists>Q'. Q\<midarrow>x\<^bold>?\<rightarrow>Q'\<close>
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
  case (Composition P Q \<mu>)
  from this(3) show ?case
  proof cases
    case (ObsOut x)
    then obtain R where *: \<open>\<^bold>!(P \<^bold>| Q) \<midarrow>x\<^bold>!\<rightarrow> R\<close> by blast
    then show ?thesis
    proof (cases \<open>observable (\<^bold>!P) \<mu>\<close>)
      case True
      then show ?thesis
        using Composition.IH TParL observable.simps by metis
    next
      case PF: False
      then show ?thesis
      proof (cases \<open>observable (\<^bold>!Q) \<mu>\<close>)
        case True
        then show ?thesis
          using Composition.IH TParR observable.simps by metis
      next
        case False
        then have NQ: \<open>\<nexists>Q'. Q \<midarrow>x\<^bold>!\<rightarrow> Q'\<close>
          using ObsOut by blast
        moreover from PF have NP: \<open>\<nexists>P'. P \<midarrow>x\<^bold>!\<rightarrow> P'\<close>
          using ObsOut by blast
        moreover from * have \<open>P \<midarrow>x\<^bold>!\<rightarrow> R \<or> Q \<midarrow>x\<^bold>!\<rightarrow> R\<close>
        proof (cases rule: transition.cases)
          case (TRep P')
          then show ?thesis
            using NP NQ par_add_obs observable.simps by blast
        qed
        ultimately have False
          by blast
        then show ?thesis ..
      qed
    qed
  next
    case (ObsIn x)
    then obtain R where *: \<open>\<^bold>!(P \<^bold>| Q) \<midarrow>x\<^bold>?\<rightarrow> R\<close> by blast
    then show ?thesis
    proof (cases \<open>observable (\<^bold>!P) \<mu>\<close>)
      case True
      then show ?thesis
        using Composition.IH TParL observable.simps by metis
    next
      case PF: False
      then show ?thesis
      proof (cases \<open>observable (\<^bold>!Q) \<mu>\<close>)
        case True
        then show ?thesis
          using Composition.IH TParR observable.simps by metis
      next
        case False
        then have NQ: \<open>\<nexists>Q'. Q \<midarrow>x\<^bold>?\<rightarrow> Q'\<close>
          using ObsIn by blast
        moreover from PF have NP: \<open>\<nexists>P'. P \<midarrow>x\<^bold>?\<rightarrow> P'\<close>
          using ObsIn by blast
        moreover from * have \<open>P \<midarrow>x\<^bold>?\<rightarrow> R \<or> Q \<midarrow>x\<^bold>?\<rightarrow> R\<close>
        proof (cases rule: transition.cases)
          case (TRep P')
          then show ?thesis
            using NP NQ par_add_obs observable.simps by blast
        qed
        ultimately have False
          by blast
        then show ?thesis ..
      qed
    qed
  qed
next
  case (Replicate P)
  from this(2) show ?case
  proof (cases)
    case (ObsOut x)
    then obtain R where \<open>\<^bold>!(\<^bold>!P) \<midarrow>x\<^bold>!\<rightarrow> R\<close> by blast
    then show ?thesis
    proof (cases)
      case (TRep P')
      then show ?thesis using ObsOut Replicate.IH
        by blast
    qed
  next
    case (ObsIn x)
    then obtain R where \<open>\<^bold>!(\<^bold>!P) \<midarrow>x\<^bold>?\<rightarrow> R\<close> by blast
    then show ?thesis
    proof (cases)
      case (TRep P')
      then show ?thesis using ObsIn Replicate.IH
        by blast
    qed
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
  then show ?case
    using names.simps(5) rep_preserves_obs by blast
qed simp

definition sim (\<open>_ \<sim>[_]\<leadsto> _\<close> [60,20,60] 50) where
  \<open>P \<sim>[Rel]\<leadsto> Q \<equiv> (\<forall>\<mu>. observable P \<mu> \<longrightarrow> observable Q \<mu>) \<and>
                   (\<forall>P'. P \<midarrow>\<tau>\<rightarrow> P' \<longrightarrow> (\<exists>Q'. Q \<midarrow>\<tau>\<rightarrow> Q' \<and> (Q',P') \<in> Rel))\<close>

lemma simCases [consumes 1, case_names Obs Sim]:
  assumes \<open>\<And>\<mu>. observable P \<mu> \<Longrightarrow> observable Q \<mu>\<close>
    and \<open>\<And>P'. P \<midarrow>\<tau>\<rightarrow> P' \<Longrightarrow> \<exists>Q'. Q \<midarrow>\<tau>\<rightarrow> Q' \<and> (Q',P') \<in> Rel\<close>
  shows \<open>P \<sim>[Rel]\<leadsto> Q\<close>
  unfolding sim_def by (simp add: assms)

lemma sim_E [elim]:
  assumes \<open>P \<sim>[Rel]\<leadsto> Q\<close>
  shows \<open>observable P \<mu> \<Longrightarrow> observable Q \<mu>\<close>
    and \<open>P \<midarrow>\<tau>\<rightarrow> P' \<Longrightarrow> \<exists>Q'. Q \<midarrow>\<tau>\<rightarrow> Q' \<and> (Q',P') \<in> Rel\<close>
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
  then have \<open>\<exists>Q'. Q\<midarrow>\<tau>\<rightarrow>Q' \<and> (Q', P') \<in> X\<close>
    using PQ by auto
  then obtain Q' where \<open>Q\<midarrow>\<tau>\<rightarrow>Q'\<close> and X: \<open>(Q', P') \<in> X\<close> by blast
  then have \<open>\<exists>R'. R\<midarrow>\<tau>\<rightarrow>R' \<and> (R', Q') \<in> Y\<close> using QR by auto
  then obtain R' where \<open>R\<midarrow>\<tau>\<rightarrow>R'\<close> and Y: \<open>(R', Q') \<in> Y\<close> by blast
  moreover have \<open>(R', P') \<in> Z\<close> using X Y XYZ by auto
  ultimately show \<open>\<exists>R'. R\<midarrow>\<tau>\<rightarrow>R' \<and> (R', P') \<in> Z\<close> by auto
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

abbreviation bisimulation (\<open>_ \<sim> _\<close> [60,60] 50) where
  \<open>P \<sim> Q \<equiv> (P,Q) \<in> bisim\<close>

lemma bisimCoinduct [case_names bisim sym, consumes 1]:
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
    case (sym R S)
    then show ?case
      using bisim_sym sympE[of bisimulation] by auto
  qed
qed

theorem bisim_equiv: \<open>equivp bisimulation\<close>
  using bisim_refl bisim_sym bisim_trans equivpI by auto

subsection \<open>Examples\<close>

lemma \<open>x\<^bold>!.y\<^bold>!.\<zero> \<sim> x\<^bold>!.\<zero>\<close> (is \<open>?P \<sim> ?Q\<close>)
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
      then show \<open>\<exists>S'. S \<midarrow>\<tau>\<rightarrow> S' \<and> (S',R') \<in> ?R\<close> ..
    qed
    then show ?case
      using monotonic by blast
  qed auto
qed

lemma \<open>\<not> (x\<^bold>!.y\<^bold>!.\<zero> \<^bold>| x\<^bold>?.\<zero> \<sim> x\<^bold>!.\<zero> \<^bold>| x\<^bold>?.\<zero>)\<close> (is \<open>\<not> (?P \<sim> ?Q)\<close>)
proof
  assume \<open>?P \<sim> ?Q\<close>
  then show False
  proof
    fix P Q
    assume \<open>Q \<sim> P\<close>
    let ?P' = \<open>y\<^bold>!.\<zero> \<^bold>| \<zero>\<close>
    assume \<open>?P = P\<close> \<open>?Q = Q\<close>
    moreover assume \<open>P \<sim>[bisim]\<leadsto> Q\<close>
    ultimately have \<open>?P \<sim>[bisim]\<leadsto> ?Q\<close>
      by simp
    then have \<open>\<And>P'. ?P \<midarrow>\<tau>\<rightarrow> P' \<Longrightarrow> \<exists>Q'. ?Q \<midarrow>\<tau>\<rightarrow> Q' \<and> (Q',P') \<in> bisim\<close>
      using sim_E by blast
    moreover have \<open>?P \<midarrow>\<tau>\<rightarrow> ?P'\<close>
      by auto
    ultimately have \<open>\<exists>Q'. ?Q \<midarrow>\<tau>\<rightarrow> Q' \<and> (Q',?P') \<in> bisim\<close>
      by auto
    then obtain Q' where \<open>?Q \<midarrow>\<tau>\<rightarrow> Q'\<close> and *: \<open>(Q',?P') \<in> bisim\<close>
      by blast
    moreover from this have \<open>Q' = \<zero> \<^bold>| \<zero>\<close>
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
      assume \<open>\<zero> \<^bold>| \<zero> = R\<close> \<open>?P' = S\<close>
      moreover assume \<open>S \<sim> R\<close>
      ultimately have \<open>?P' \<sim>[bisim]\<leadsto> \<zero> \<^bold>| \<zero>\<close> by fast
      then have \<open>observable ?P' (OOut y) \<Longrightarrow> observable (\<zero> \<^bold>| \<zero>) (OOut y)\<close>
        using sim_E by blast
      then have \<open>observable (\<zero> \<^bold>| \<zero>) (OOut y)\<close> by blast
      then have \<open>observable \<zero> (OOut y)\<close>
        using par_add_obs by blast
      then show False by simp
    qed
  qed
qed

lemma \<open>\<^bold>!(x\<^bold>!.\<zero> \<^bold>| x\<^bold>?.\<zero>) \<sim> \<^bold>!x\<^bold>!.\<zero> \<^bold>| \<^bold>!x\<^bold>?.\<zero>\<close> (is \<open>?P \<sim> ?Q\<close>)
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
          then have R: \<open>R = ?Q\<close>
            using bisim by simp
          then show ?thesis using bisim
          proof (cases S)
            case (Replicate P')
            then have \<open>S = ?P\<close>
              using bisim by simp
            moreover from OOut * have \<open>x' = x\<close>
              by (metis R in_not_obs_out obs_out_eq par_add_obs rep_preserves_obs)
            ultimately show ?thesis using * R OOut
              by blast
          qed simp_all
        next
          case (Replicate P')
          then have R: \<open>R = ?P\<close>
            using bisim by simp
          then show ?thesis using bisim
          proof (cases S)
            case (Composition P Q)
            then have \<open>S = ?Q\<close>
              using bisim by simp
            moreover from OOut * have \<open>x' = x\<close>
              by (metis R in_not_obs_out obs_out_eq par_add_obs rep_preserves_obs)
            ultimately show ?thesis using * R OOut by blast
          qed simp_all
        qed simp_all
      next
        case (OIn x')
        then show ?thesis
          using bisim
        proof (cases R)
          case (Composition P Q)
          then have R: \<open>R = ?Q\<close>
            using bisim by simp
          then show ?thesis using bisim
          proof (cases S)
            case (Replicate P')
            then have \<open>S = ?P\<close>
              using bisim by simp
            moreover from OIn * have \<open>x' = x\<close>
              by (metis R obs_in_eq out_not_obs_in par_add_obs rep_preserves_obs)
            ultimately show ?thesis using * R OIn
              by blast
          qed simp_all
        next
          case (Replicate P')
          then have R: \<open>R = ?P\<close>
            using bisim by simp
          then show ?thesis using bisim
          proof (cases S)
            case (Composition P Q)
            then have \<open>S = ?Q\<close>
              using bisim by simp
            moreover from OIn * have \<open>x' = x\<close>
              by (metis R obs_in_eq out_not_obs_in par_add_obs rep_preserves_obs)
            ultimately show ?thesis using * R OIn by blast
          qed simp_all
        qed simp_all
      qed
    next
      fix R'
      assume \<open>R \<midarrow>\<tau>\<rightarrow> R'\<close>
      then show \<open>\<exists>S'. S \<midarrow>\<tau>\<rightarrow> S' \<and> (S',R') \<in> ?R\<close>
        using bisim
      proof (cases S)
        case (Composition P Q)
        then have S: \<open>S = ?Q\<close> using bisim by simp
        then have \<open>S \<midarrow>\<tau>\<rightarrow> (\<zero> \<^bold>| \<^bold>!x\<^bold>!.\<zero>) \<^bold>| (\<zero> \<^bold>| \<^bold>!x\<^bold>?.\<zero>)\<close>
          by blast
        then show ?thesis
          sorry
      next
        case (Replicate P)
        then show ?thesis sorry
      qed simp_all
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

primrec apply_ctx (\<open>_\<lbrakk>_\<rbrakk>\<close> [400,100] 200) where
  \<open>apply_ctx CHole P = P\<close>
| \<open>apply_ctx CInaction P = \<zero>\<close>
| \<open>apply_ctx (COut x C) P = x\<^bold>!.C\<lbrakk>P\<rbrakk>\<close>
| \<open>apply_ctx (CIn x C) P = x\<^bold>?.C\<lbrakk>P\<rbrakk>\<close>
| \<open>apply_ctx (CComposition C\<^sub>1 C\<^sub>2) P = C\<^sub>1\<lbrakk>P\<rbrakk> \<^bold>| C\<^sub>2\<lbrakk>P\<rbrakk>\<close>
| \<open>apply_ctx (CReplicate C) P = \<^bold>!C\<lbrakk>P\<rbrakk>\<close>

lemma apply_ctx_no_holes [simp]: \<open>ctx_holes C = 0 \<Longrightarrow> C\<lbrakk>P\<rbrakk> = C\<lbrakk>Q\<rbrakk>\<close>
  by (induction C) simp_all

primrec apply_ctx_ctx where
  \<open>apply_ctx_ctx CHole C' = C'\<close>
| \<open>apply_ctx_ctx CInaction C' = CInaction\<close>
| \<open>apply_ctx_ctx (COut x C) C' = COut x (apply_ctx_ctx C C')\<close>
| \<open>apply_ctx_ctx (CIn x C) C' = CIn x (apply_ctx_ctx C C')\<close>
| \<open>apply_ctx_ctx (CComposition C1 C2) C' = CComposition (apply_ctx_ctx C1 C') (apply_ctx_ctx C2 C')\<close>
| \<open>apply_ctx_ctx (CReplicate C) C' = CReplicate (apply_ctx_ctx C C')\<close>

lemma apply_ctx_ctx_no_holes [simp]: \<open>ctx_holes C = 0 \<Longrightarrow> apply_ctx_ctx C C' = C\<close>
  by (induction C) simp_all

lemma apply_ctx_ctx_wf [simp]: \<open>wf_ctx C \<Longrightarrow> wf_ctx C' \<Longrightarrow> wf_ctx (apply_ctx_ctx C C')\<close>
proof (induction C)
  case (CComposition C1 C2)
  then show ?case
    using add_is_1 by fastforce
qed simp_all

primrec process_to_ctx where
  \<open>process_to_ctx Inaction = CInaction\<close>
| \<open>process_to_ctx (Out x P) = COut x (process_to_ctx P)\<close>
| \<open>process_to_ctx (In x P) = CIn x (process_to_ctx P)\<close>
| \<open>process_to_ctx (Composition P Q) = CComposition (process_to_ctx P) (process_to_ctx Q)\<close>
| \<open>process_to_ctx (Replicate P) = CReplicate (process_to_ctx P)\<close>

lemma process_to_ctx_apply[simp]: \<open>\<forall>R. (process_to_ctx P)\<lbrakk>R\<rbrakk> = P\<close>
  by (induction P) simp_all

lemma process_to_ctx_0_holes[simp]: \<open>ctx_holes (process_to_ctx P) = 0\<close>
  by (induction P) simp_all

definition congruence where
  \<open>congruence S \<equiv> (\<forall>(P,Q) \<in> S. (\<forall>C. wf_ctx C \<longrightarrow> (C\<lbrakk>P\<rbrakk>, C\<lbrakk>Q\<rbrakk>) \<in> S))\<close>

section \<open>Strong barbed congruence\<close>

coinductive_set sbcong where
  \<open>(\<forall>C. wf_ctx C \<longrightarrow> C\<lbrakk>P\<rbrakk> \<sim> C\<lbrakk>Q\<rbrakk>) \<Longrightarrow> (P,Q) \<in> sbcong\<close>

abbreviation sbcongruence (\<open>_ \<simeq> _\<close> [50,50] 30) where
  \<open>P \<simeq> Q \<equiv> (P,Q) \<in> sbcong\<close>

lemma sbcong_E [elim]: \<open>P \<simeq> Q \<Longrightarrow> wf_ctx C \<Longrightarrow> C\<lbrakk>P\<rbrakk> \<sim> C\<lbrakk>Q\<rbrakk>\<close>
  by (meson sbcong.cases)

lemma sbcong_out [simp]: \<open>P \<simeq> Q \<Longrightarrow> x\<^bold>!.P \<simeq> x\<^bold>!.Q\<close>
proof (coinduction)
  case sbcong
  then have *: \<open>\<forall>C. wf_ctx C \<longrightarrow> C\<lbrakk>P\<rbrakk> \<sim> C\<lbrakk>Q\<rbrakk>\<close>
    by auto
  then have \<open>\<forall>C. wf_ctx C \<longrightarrow> C\<lbrakk>x\<^bold>!.P\<rbrakk> \<sim> C\<lbrakk>x\<^bold>!.Q\<rbrakk>\<close>
  proof (clarify)
    fix C
    let ?C = \<open>apply_ctx_ctx C (COut x CHole)\<close>
    assume \<open>wf_ctx C\<close>
    then have \<open>wf_ctx ?C\<close>
      by simp
    moreover have \<open>C\<lbrakk>x\<^bold>!.P\<rbrakk> = ?C\<lbrakk>P\<rbrakk>\<close>
    proof (induction C)
      case (CComposition C1 C2)
      then show ?case
        by (cases \<open>wf_ctx C1\<close>) simp_all
    qed simp_all
    moreover have \<open>C\<lbrakk>x\<^bold>!.Q\<rbrakk> = ?C\<lbrakk>Q\<rbrakk>\<close>
    proof (induction C)
      case (CComposition C1 C2)
      then show ?case
        by (cases \<open>wf_ctx C1\<close>) simp_all
    qed simp_all
    ultimately show \<open>C\<lbrakk>x\<^bold>!.P\<rbrakk> \<sim> C\<lbrakk>x\<^bold>!.Q\<rbrakk>\<close>
      using * by simp
  qed
  then show ?case
    by blast
qed

lemma sbcong_in [simp]: \<open>P \<simeq> Q \<Longrightarrow> x\<^bold>?.P \<simeq> x\<^bold>?.Q\<close>
proof (coinduction)
  case sbcong
  then have *: \<open>\<forall>C. wf_ctx C \<longrightarrow> C\<lbrakk>P\<rbrakk> \<sim> C\<lbrakk>Q\<rbrakk>\<close>
    by auto
  then have \<open>\<forall>C. wf_ctx C \<longrightarrow> C\<lbrakk>x\<^bold>?.P\<rbrakk> \<sim> C\<lbrakk>x\<^bold>?.Q\<rbrakk>\<close>
  proof (clarify)
    fix C
    let ?C = \<open>apply_ctx_ctx C (CIn x CHole)\<close>
    assume \<open>wf_ctx C\<close>
    then have \<open>wf_ctx ?C\<close>
      by simp
    moreover have \<open>C\<lbrakk>x\<^bold>?.P\<rbrakk> = ?C\<lbrakk>P\<rbrakk>\<close>
    proof (induction C)
      case (CComposition C1 C2)
      then show ?case
        by (cases \<open>wf_ctx C1\<close>) simp_all
    qed simp_all
    moreover have \<open>C\<lbrakk>x\<^bold>?.Q\<rbrakk> = ?C\<lbrakk>Q\<rbrakk>\<close>
    proof (induction C)
      case (CComposition C1 C2)
      then show ?case
        by (cases \<open>wf_ctx C1\<close>) simp_all
    qed simp_all
    ultimately show \<open>C\<lbrakk>x\<^bold>?.P\<rbrakk> \<sim> C\<lbrakk>x\<^bold>?.Q\<rbrakk>\<close>
      using * by simp
  qed
  then show ?case
    by blast
qed

lemma sbcong_rep [simp]: \<open>P \<simeq> Q \<Longrightarrow> \<^bold>!P \<simeq> \<^bold>!Q\<close>
proof (coinduction)
  case sbcong
  then have *: \<open>\<forall>C. wf_ctx C \<longrightarrow> C\<lbrakk>P\<rbrakk> \<sim> C\<lbrakk>Q\<rbrakk>\<close>
    by auto
  then have \<open>\<forall>C. wf_ctx C \<longrightarrow> C\<lbrakk>\<^bold>!P\<rbrakk> \<sim> C\<lbrakk>\<^bold>!Q\<rbrakk>\<close>
  proof (clarify)
    fix C
    let ?C = \<open>apply_ctx_ctx C (CReplicate CHole)\<close>
    assume \<open>wf_ctx C\<close>
    then have \<open>wf_ctx ?C\<close>
      by simp
    moreover have \<open>C\<lbrakk>\<^bold>!P\<rbrakk> = ?C\<lbrakk>P\<rbrakk>\<close>
    proof (induction C)
      case (CComposition C1 C2)
      then show ?case
        by (cases \<open>wf_ctx C1\<close>) simp_all
    qed simp_all
    moreover have \<open>C\<lbrakk>\<^bold>!Q\<rbrakk> = ?C\<lbrakk>Q\<rbrakk>\<close>
    proof (induction C)
      case (CComposition C1 C2)
      then show ?case
        by (cases \<open>wf_ctx C1\<close>) simp_all
    qed simp_all
    ultimately show \<open>C\<lbrakk>\<^bold>!P\<rbrakk> \<sim> C\<lbrakk>\<^bold>!Q\<rbrakk>\<close>
      using * by simp
  qed
  then show ?case
    by blast
qed

lemma sbcong_cong: \<open>congruence sbcong\<close>
  unfolding congruence_def
proof (safe)
  fix P Q C
  assume \<open>P \<simeq> Q\<close>
  moreover assume \<open>wf_ctx C\<close>
  ultimately show \<open>C\<lbrakk>P\<rbrakk> \<simeq> C\<lbrakk>Q\<rbrakk>\<close>
  proof (induction C)
    case (CComposition C\<^sub>1 C\<^sub>2)
    then show ?case
    proof (cases \<open>wf_ctx C\<^sub>1\<close>)
      case True
      then have \<open>C\<^sub>1\<lbrakk>P\<rbrakk> \<simeq> C\<^sub>1\<lbrakk>Q\<rbrakk>\<close>
        using CComposition by simp
      moreover from True have *: \<open>ctx_holes C\<^sub>2 = 0\<close>
        using CComposition by simp
      then have \<open>C\<^sub>2\<lbrakk>P\<rbrakk> = C\<^sub>2\<lbrakk>\<zero>\<rbrakk>\<close>
        by simp
      then have \<open>CComposition C\<^sub>1 C\<^sub>2\<lbrakk>P\<rbrakk> = C\<^sub>1\<lbrakk>P\<rbrakk> \<^bold>| C\<^sub>2\<lbrakk>\<zero>\<rbrakk>\<close>
        by simp
      moreover from * have \<open>C\<^sub>2\<lbrakk>Q\<rbrakk> = C\<^sub>2\<lbrakk>\<zero>\<rbrakk>\<close>
        by simp
      then have \<open>CComposition C\<^sub>1 C\<^sub>2\<lbrakk>Q\<rbrakk> = C\<^sub>1\<lbrakk>Q\<rbrakk> \<^bold>| C\<^sub>2\<lbrakk>\<zero>\<rbrakk>\<close>
        by simp
      moreover have \<open>C\<^sub>1\<lbrakk>P\<rbrakk> \<^bold>| C\<^sub>2\<lbrakk>\<zero>\<rbrakk> \<simeq> C\<^sub>1\<lbrakk>Q\<rbrakk> \<^bold>| C\<^sub>2\<lbrakk>\<zero>\<rbrakk>\<close>
        sorry
      ultimately show ?thesis
        by simp
    next
      case False
      then have \<open>ctx_holes C\<^sub>1 = 0\<close>
        using CComposition by simp
      then show ?thesis
        sorry
    qed
  qed simp_all
qed

lemma sbcong_sym: \<open>symp sbcongruence\<close>
proof
  fix P Q
  assume \<open>P \<simeq> Q\<close>
  then have *: \<open>\<forall>C. wf_ctx C \<longrightarrow> C\<lbrakk>P\<rbrakk> \<sim> C\<lbrakk>Q\<rbrakk>\<close>
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

lemma sbcong_bisim[simp]: \<open>P \<simeq> Q \<Longrightarrow> P \<sim> Q\<close>
proof -
  assume \<open>(P,Q) \<in> sbcong\<close>
  then show \<open>P \<sim> Q\<close>
  proof (coinduct rule: bisimCoinduct)
    case (bisim R S)
    then show ?case sorry
  next
    case (sym R S)
    then show ?case
      using sbcong_sym by (meson symp_def)
  qed
qed

lemma bisim_contract_inaction: \<open>P \<sim> P \<^bold>| \<zero>\<close>
proof -
  have \<open>P \<sim> P\<close>
    using bisim_refl unfolding reflp_def by simp
  then have \<open>P \<sim>[bisim]\<leadsto> P\<close>
    by fast
  then have \<open>\<And>\<mu>. observable P \<mu> \<Longrightarrow> observable P \<mu>\<close>
    \<open>\<And>P'. P \<midarrow>\<tau>\<rightarrow> P' \<Longrightarrow> \<exists>Q'. P \<midarrow>\<tau>\<rightarrow> Q' \<and> (Q',P') \<in> bisim\<close>
    using sim_E by blast+
  then have \<open>P \<sim>[bisim]\<leadsto> P \<^bold>| \<zero>\<close>
    unfolding sim_def
    sorry
  then show ?thesis
    sorry
qed

lemma sbcong_largest: \<open>congruence S \<and> S \<subseteq> bisim \<Longrightarrow> S \<subseteq> sbcong\<close>
  using congruence_def sbcong.simps by fastforce

theorem challenge: \<open>P \<simeq> Q \<longleftrightarrow> (\<forall>R. P \<^bold>| R \<sim> Q \<^bold>| R)\<close>
proof (safe)
  fix R
  let ?C = \<open>CComposition CHole (process_to_ctx R)\<close>
  have \<open>wf_ctx ?C\<close>
    by simp
  moreover assume \<open>P \<simeq> Q\<close>
  ultimately have \<open>?C\<lbrakk>P\<rbrakk> \<simeq> ?C\<lbrakk>Q\<rbrakk>\<close>
    using sbcong_cong unfolding congruence_def by blast
  then show \<open>P \<^bold>| R \<sim> Q \<^bold>| R\<close>
    by (simp add: congruence_def)
next
  assume *: \<open>\<forall>R. P \<^bold>| R \<sim> Q \<^bold>| R\<close>
  show \<open>P \<simeq> Q\<close>
  proof (rule sbcong.intros, safe)
    fix C
    assume \<open>wf_ctx C\<close>
    then show \<open>C\<lbrakk>P\<rbrakk> \<sim> C\<lbrakk>Q\<rbrakk>\<close>
    proof (induction C)
      case CHole
      from * have \<open>P \<^bold>| \<zero> \<sim> Q \<^bold>| \<zero>\<close>
        by blast
      moreover have \<open>P \<^bold>| \<zero> \<sim> P\<close>
        using bisim_contract_inaction bisim_sym symp_def by metis
      moreover have \<open>Q \<sim> Q \<^bold>| \<zero>\<close>
        using bisim_contract_inaction by metis
      ultimately have \<open>P \<sim> Q\<close>
        by (metis (no_types, lifting) bisim_equiv equivp_def)
      then show ?case
        by simp
    next
      case CInaction
      then show ?case
        by simp
    next
      case (COut x1 C)
      then have \<open>C\<lbrakk>P\<rbrakk> \<sim> C\<lbrakk>Q\<rbrakk>\<close>
        by simp
      then show ?case
        
        sorry
    next
      case (CIn x1 C)
      then show ?case sorry
    next
      case (CComposition C1 C2)
      then show ?case sorry
    next
      case (CReplicate C)
      then show ?case sorry
    qed
  qed
qed

end