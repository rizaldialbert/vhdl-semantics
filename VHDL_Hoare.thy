(*
 * Copyright 2018, NTU
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 *  Author: Albert Rizaldi, NTU Singapore
 *)

theory VHDL_Hoare
  imports Femto_VHDL
begin

subsection \<open>Hoare Logic for @{typ "'signal seq_stmt"}\<close>

type_synonym 'signal worldline = "'signal \<Rightarrow> nat \<Rightarrow> val"

definition worldline_upd :: "'signal worldline \<Rightarrow> 'signal \<Rightarrow> nat \<Rightarrow> val \<Rightarrow> 'signal worldline" ("_[_, _:= _]") where
  "worldline_upd w s t v = (\<lambda>s' t'. if s' \<noteq> s \<or> t' < t then w s' t' else v)"

definition worldline_inert_upd :: "'signal worldline \<Rightarrow> 'signal \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> val \<Rightarrow> 'signal worldline" ("_[_, _, _ := _]") where
  "worldline_inert_upd w s t t0 v = (\<lambda>s' t'. if s' \<noteq> s \<or> t' < t0 then w s' t' else if t' < t then w s' t0 else v)"

type_synonym 'signal assn = "'signal worldline \<Rightarrow> bool"

definition state_of_world :: "'signal worldline \<Rightarrow> nat \<Rightarrow> 'signal state" where
  "state_of_world w t = (\<lambda>s. w s t)"

definition event_of_world :: "'signal worldline \<Rightarrow> nat \<Rightarrow> 'signal event" where
  "event_of_world w t = (if t = 0 then {s :: 'signal. w s 0 \<noteq> False} else {s :: 'signal. w s t \<noteq> w s (t - 1)})"

definition beh_of_world_raw :: "'signal worldline \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> 'signal \<rightharpoonup> val" where
  "beh_of_world_raw w t = (\<lambda>t'. if t' < t then (\<lambda>s. Some (w s t')) else Map.empty)"

lift_definition beh_of_world :: "'signal worldline \<Rightarrow> nat \<Rightarrow> 'signal transaction" is beh_of_world_raw
  unfolding beh_of_world_raw_def zero_map by auto

lemma [simp]:
  "beh_of_world w 0 = 0"
  by (transfer', auto simp add:  beh_of_world_raw_def zero_option_def zero_fun_def)

definition beval_world :: "'signal worldline \<Rightarrow> nat \<Rightarrow> 'signal bexp \<Rightarrow> val" where
  "beval_world w t exp = beval t (state_of_world w t) (event_of_world w t) (beh_of_world w t) exp"

definition trans_of_world_raw :: "'signal worldline \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> 'signal \<rightharpoonup> val" where
  "trans_of_world_raw w t = (\<lambda>t'. if t \<le> t' then undefined else Map.empty)"

inductive
  seq_hoare :: "nat \<Rightarrow> 'signal assn \<Rightarrow> 'signal seq_stmt \<Rightarrow> 'signal assn \<Rightarrow> bool" ("\<turnstile>\<^sub>_ ({(1_)}/ (_)/ {(1_)})" 50)
  where
Null: "\<turnstile>\<^sub>t {P} Bnull {P}" |

Assign: "\<turnstile>\<^sub>t {\<lambda>w. P(w[sig, t + dly := beval_world w t exp])} Bassign_trans sig exp dly {P}" |

AssignI: "\<turnstile>\<^sub>t {\<lambda>w. P(w[sig, t + dly, t := beval_world w t exp])} Bassign_inert sig exp dly {P}" |

Comp: "\<lbrakk> \<turnstile>\<^sub>t {P} s1 {Q}; \<turnstile>\<^sub>t {Q} s2 {R}\<rbrakk> \<Longrightarrow> \<turnstile>\<^sub>t {P} Bcomp s1 s2 {R}" |

If: "\<lbrakk>\<turnstile>\<^sub>t {\<lambda>w. P w \<and> beval_world w t g} s1 {Q}; \<turnstile>\<^sub>t {\<lambda>w. P w \<and> \<not> beval_world w t  g} s2 {Q}\<rbrakk>
        \<Longrightarrow>  \<turnstile>\<^sub>t {P} Bguarded g s1 s2 {Q}" |

Conseq: "\<lbrakk>\<forall>w. P' w \<longrightarrow> P w; \<turnstile>\<^sub>t {P} s {Q}; \<forall>w. Q w \<longrightarrow> Q' w\<rbrakk> \<Longrightarrow> \<turnstile>\<^sub>t {P'} s {Q'}"

inductive_cases seq_hoare_ic: "\<turnstile>\<^sub>t {P} s {Q}"

lemma BnullE:
  assumes "\<turnstile>\<^sub>t {P} s {Q}"
  assumes "s = Bnull"
  shows "\<forall>w. P w \<longrightarrow> Q w"
  using assms
  by (induction rule:seq_hoare.induct, auto)

lemma BnullE':
  "\<turnstile>\<^sub>t {P} Bnull {Q} \<Longrightarrow> \<forall>w. P w \<longrightarrow> Q w"
  using BnullE by blast

lemma BassignE:
  assumes "\<turnstile>\<^sub>t {P} s {Q}"
  assumes "s = Bassign_trans sig exp dly"
  shows "\<forall>w. P w \<longrightarrow> Q(w[sig, t + dly := beval_world w t exp])"
  using assms
  by (induction rule: seq_hoare.induct, auto)

lemma Bassign_inertE:
  assumes "\<turnstile>\<^sub>t {P} s {Q}"
  assumes "s = Bassign_inert sig exp dly"
  shows "\<forall>w. P w \<longrightarrow> Q(w[sig, t + dly, t := beval_world w t exp])"
  using assms
  by (induction rule: seq_hoare.induct, auto)

lemma BcompE:
  assumes "\<turnstile>\<^sub>t {P} s {R}"
  assumes "s = Bcomp s1 s2"
  shows "\<exists>Q. \<turnstile>\<^sub>t {P} s1 {Q} \<and> \<turnstile>\<^sub>t {Q} s2 {R}"
  using assms Conseq
  by (induction rule:seq_hoare.induct, auto) (blast)

lemmas [simp] = seq_hoare.Null seq_hoare.Assign seq_hoare.Comp seq_hoare.If
lemmas [intro!] = seq_hoare.Null seq_hoare.Assign seq_hoare.Comp seq_hoare.If

lemma strengthen_pre:
  assumes "\<forall>w. P' w \<longrightarrow> P w" and "\<turnstile>\<^sub>t {P} s {Q}"
  shows "\<turnstile>\<^sub>t {P'} s {Q}"
  using assms by (blast intro: Conseq)

lemma weaken_post:
  assumes "\<forall>w. Q w \<longrightarrow> Q' w" and "\<turnstile>\<^sub>t {P} s {Q}"
  shows "\<turnstile>\<^sub>t {P} s {Q'}"
  using assms by (blast intro: Conseq)

lemma Assign':
  assumes "\<forall>w. P w \<longrightarrow> Q (worldline_upd w sig (t + dly) (beval_world w t exp))"
  shows "\<turnstile>\<^sub>t {P} Bassign_trans sig exp dly {Q}"
  using assms by (simp add: strengthen_pre)

subsection \<open>Validity of Hoare proof rules\<close>

definition worldline :: "nat \<Rightarrow> 'signal state \<Rightarrow> 'signal transaction \<Rightarrow> 'signal transaction \<Rightarrow> 'signal worldline" where
  "worldline t \<sigma> \<theta> \<tau> = (\<lambda>s' t'. if t' < t then signal_of2 False \<theta> s' t' else signal_of2 (\<sigma> s') \<tau> s' t')"

definition
seq_hoare_valid :: "nat \<Rightarrow> 'signal assn \<Rightarrow> 'signal seq_stmt \<Rightarrow> 'signal assn \<Rightarrow> bool" ("\<Turnstile>\<^sub>_ {(1_)}/ (_)/ {(1_)}" 50)
  where "\<Turnstile>\<^sub>t {P} s {Q} \<longleftrightarrow>  (\<forall>\<sigma> \<tau> \<gamma> \<theta> \<tau>' w w'.  context_invariant t \<sigma> \<gamma> \<theta> \<tau>
                                            \<and>  w = worldline t \<sigma> \<theta> \<tau>
                                            \<and>  P w
                                            \<and> (t, \<sigma>, \<gamma>, \<theta> \<turnstile> <s, \<tau>> \<longrightarrow>\<^sub>s \<tau>')
                                            \<and>  w' = worldline t \<sigma> \<theta> \<tau>' \<longrightarrow> Q w')"

lemma Bcomp_hoare_valid:
  assumes "\<Turnstile>\<^sub>t {P} s1 {Q}" and "\<Turnstile>\<^sub>t {Q} s2 {R}"
  assumes "nonneg_delay (Bcomp s1 s2)"
  shows "\<Turnstile>\<^sub>t {P} Bcomp s1 s2 {R}"
  unfolding seq_hoare_valid_def
proof (rule)+
  fix \<sigma> :: "'a state"
  fix \<tau> \<theta> \<tau>' :: "'a transaction"
  fix \<gamma> :: "'a event"
  fix w w' :: "'a worldline"
  assume "context_invariant t \<sigma> \<gamma> \<theta> \<tau> \<and> w = worldline t \<sigma> \<theta> \<tau> \<and> P w \<and>
          t , \<sigma> , \<gamma> , \<theta> \<turnstile> <Bcomp s1 s2 , \<tau>> \<longrightarrow>\<^sub>s \<tau>' \<and> w' = worldline t \<sigma> \<theta> \<tau>'"
  hence "context_invariant t \<sigma> \<gamma> \<theta> \<tau>" and "w = worldline t \<sigma> \<theta> \<tau>" and "P w"
    and "t , \<sigma> , \<gamma> , \<theta> \<turnstile> <Bcomp s1 s2 , \<tau>> \<longrightarrow>\<^sub>s \<tau>' " and 2: "w' = worldline t \<sigma> \<theta> \<tau>'"
    by auto
  then obtain \<tau>'' where 0: "t, \<sigma>, \<gamma>, \<theta> \<turnstile> <s1, \<tau>> \<longrightarrow>\<^sub>s \<tau>''" and 1: "t, \<sigma>, \<gamma>, \<theta> \<turnstile> <s2, \<tau>''> \<longrightarrow>\<^sub>s \<tau>'"
    by auto
  define w'' where "w'' = worldline t \<sigma> \<theta> \<tau>''"
  hence "Q w''"
    using `\<Turnstile>\<^sub>t {P} s1 {Q}` unfolding seq_hoare_valid_def
    using \<open>P w\<close> \<open>context_invariant t \<sigma> \<gamma> \<theta> \<tau>\<close> \<open>t , \<sigma> , \<gamma> , \<theta> \<turnstile> <s1 , \<tau>> \<longrightarrow>\<^sub>s \<tau>''\<close> \<open>w = worldline t \<sigma> \<theta> \<tau>\<close>
    by blast
  have "context_invariant t \<sigma> \<gamma> \<theta> \<tau>''"
    using b_seq_exec_preserves_context_invariant[OF `context_invariant t \<sigma> \<gamma> \<theta> \<tau>` 0] assms(3)
    by auto
  thus "R w'"
    using `\<Turnstile>\<^sub>t {Q} s2 {R}` `w'' = worldline t \<sigma> \<theta> \<tau>''` `Q w''` 1 2 unfolding seq_hoare_valid_def
    by auto
qed

(*      Relationship between w, \<tau>, \<tau>', and w'  in seq_hoare_valid
 *
 *         P w             \<longrightarrow>               Q w
 *          \<up>                                 \<up>
 * w = worldline t \<sigma> \<theta> \<tau>          w' = worldline t \<sigma> \<theta> \<tau>'
 *          \<up>                                 \<up>
 *          \<tau>              \<longrightarrow>\<^sub>c               \<tau>'
 *
 *)

lemma Bnull_sound:
  "\<turnstile>\<^sub>t {P} Bnull {Q} \<Longrightarrow> \<Turnstile>\<^sub>t {P} Bnull {Q}"
  by (auto dest!: BnullE' simp add: seq_hoare_valid_def)

lemma state_of_world:
  assumes "w = worldline t \<sigma> \<theta> \<tau>"
  assumes "\<And>n. n < t \<Longrightarrow> lookup \<tau> n = 0"
  assumes "\<And>s. s \<in> dom (lookup \<tau> t) \<Longrightarrow> \<sigma> s = the (lookup \<tau> t s)"
  shows "state_of_world w t = \<sigma>"
proof
  fix x
  have "signal_of2 (\<sigma> x) \<tau> x t = \<sigma> x"
  proof (cases "lookup (to_transaction2 \<tau> x) t = 0")
    case True
    hence "\<forall>k \<in> dom (lookup (to_transaction2 \<tau> x)). t \<le> k"
      using assms(2) apply transfer' unfolding to_trans_raw2_def
      by (metis (full_types) domIff not_less zero_map)
    moreover have "t \<notin> dom (lookup (to_transaction2 \<tau> x))"
      using True  by (simp add: domIff zero_option_def)
    ultimately have "\<forall>k \<in> dom (lookup (to_transaction2 \<tau> x)). t < k"
      using nat_less_le by auto
    hence "inf_time (to_transaction2 \<tau>) x t = None"
      by (auto intro:inf_time_noneI)
    thus "signal_of2 (\<sigma> x) \<tau> x t = \<sigma> x"
      unfolding to_signal2_def comp_def by auto
  next
    case False
    hence "x \<in> dom (get_trans \<tau> t)"
      by (transfer', simp add: domIff zero_option_def to_trans_raw2_def)
    hence "\<sigma> x = the (lookup \<tau> t x)"
      using assms(3) by auto
    hence "lookup \<tau> t x = (Some \<circ> \<sigma>) x"
      using \<open>x \<in> dom (get_trans \<tau> t)\<close> domIff by auto
    thus "signal_of2 (\<sigma> x) \<tau> x t = \<sigma> x"
      using lookup_some_signal_of2' by fastforce
  qed
  thus "state_of_world w t x = \<sigma> x"
    unfolding state_of_world_def assms worldline_def by auto
qed

lemma beval_beh_of_world:
  assumes "w = worldline t \<sigma> \<theta> \<tau>"
  assumes "\<And>n. t \<le> n \<Longrightarrow> lookup \<theta> n = 0"
  shows "beval t \<sigma> \<gamma> (beh_of_world w t) exp = beval t \<sigma> \<gamma> \<theta> exp"
  using assms
proof (induction exp)
  case (Bsig_delayed sig n)
  have "t , \<sigma> , \<gamma> , beh_of_world w t \<turnstile> Bsig_delayed sig n \<longrightarrow>\<^sub>b signal_of2 False (beh_of_world w t) sig (t - n)"
    by auto
  have *: "beval t \<sigma> \<gamma> \<theta> (Bsig_delayed sig n) = signal_of2 False \<theta> sig (t - n)"
    by auto
  have "0 < n \<and> 0 < t \<or> (t \<noteq> 0 \<and> n = 0) \<or> t = 0"
    by auto
  moreover
  { assume "0 < n \<and> 0 < t"
    hence "get_trans (beh_of_world w t) (t - n) = Some \<circ> (\<lambda>s. w s (t - n))"
      apply transfer' unfolding beh_of_world_raw_def comp_def by auto
    hence "signal_of2 False (beh_of_world w t) sig (t - n) = w sig (t - n)"
      by (auto dest!: lookup_some_signal_of2)
    also have "... = signal_of2 False \<theta> sig (t - n)"
      using `0 < n \<and> 0 < t` unfolding assms worldline_def by auto
    also have "... = beval t \<sigma> \<gamma> \<theta> (Bsig_delayed sig n)"
      using * by auto
    finally have "signal_of2 False (beh_of_world w t) sig (t - n) = beval t \<sigma> \<gamma> \<theta> (Bsig_delayed sig n)"
      by auto
    hence ?case by auto }

  moreover
  { assume "t \<noteq> 0 \<and> n = 0 \<or> t = 0"
    moreover
    { assume "t = 0"
      hence "t - n = 0" by auto
      have "beh_of_world w t = 0" unfolding `t = 0` by auto
      hence "signal_of2 False (beh_of_world w t) sig (t - n) = signal_of2 False 0 sig 0"
        unfolding `t - n = 0` by auto
      also have "... = False"
        using signal_of2_empty[of "False" "sig" "0"] by auto
      finally have "signal_of2 False (beh_of_world w t) sig (t - n) = False"
        by auto
      have "\<theta> = 0"
        using assms(2) unfolding `t = 0` by (transfer', auto)
      hence "beval t \<sigma> \<gamma> \<theta> (Bsig_delayed sig n) = signal_of2 False \<theta> sig 0"
        using `t - n = 0` by auto
      also have "... = False"
        unfolding `\<theta> = 0` using signal_of2_empty[of "False"] by metis
      finally have "beval t \<sigma> \<gamma> \<theta> (Bsig_delayed sig n) = False"
        by auto
      hence ?case
        using `signal_of2 False (beh_of_world w t) sig (t - n) = False` by auto }
    moreover
    { assume "t \<noteq> 0 \<and> n = 0"
      have "lookup \<theta> t = 0"
        using assms(2) by auto
      have "lookup (beh_of_world w t) t = 0"
        apply transfer' unfolding beh_of_world_raw_def
        by (metis (full_types) less_not_refl map_add_subsumed1 map_add_subsumed2 map_le_def zero_map)
      have *: "lookup (beh_of_world w t) (t - 1) = Some o (\<lambda>s. w s (t - 1))"
        using `t \<noteq> 0 \<and> n = 0` apply transfer' unfolding beh_of_world_raw_def by auto
      have "signal_of2 False (beh_of_world w t) sig (t - n) = signal_of2 False (beh_of_world w t) sig t"
        using `t \<noteq> 0 \<and> n = 0` by auto
      also have "... = signal_of2 False (beh_of_world w t) sig (t - 1)"
        using signal_of2_less[OF `lookup (beh_of_world w t) t = 0`] by metis
      also have "... = w sig (t - 1)"
        using * by(auto dest!: lookup_some_signal_of2)
      also have "... = signal_of2 False \<theta> sig (t - 1)"
        using `t \<noteq> 0 \<and> n = 0` unfolding assms(1) worldline_def by auto
      also have "... = signal_of2 False \<theta> sig t"
        using signal_of2_less[OF `lookup \<theta> t = 0`] by metis
      also have "... = signal_of2 False \<theta> sig (t - n)"
        using `t \<noteq> 0 \<and> n = 0` by auto
      finally have "signal_of2 False (beh_of_world w t) sig (t - n) = signal_of2 False \<theta> sig (t - n)"
        by auto
      hence ?case
        by auto }
    ultimately have ?case by auto }
  ultimately show ?case by auto
qed (auto)

text \<open>Note that the definition of @{term "\<gamma>"} below will only be preserved by VHDL code which does
not contain a zero time signal assignment. That is, in every assignment statement, be it of transport
or inertial type, must have nonzero delay. Check @{thm "context_invariant"} and note the assumption
@{term "t < next_time t \<tau>'"}.\<close>

lemma beval_beval_world:
  assumes "w = worldline t \<sigma> \<theta> \<tau>"
  assumes "\<And>n. n < t \<Longrightarrow> lookup \<tau> n = 0"
  assumes gam: "\<gamma> = {s. \<sigma> s \<noteq> signal_of2 False \<theta> s (t - 1)}"
  assumes "\<And>s. s \<in> dom (lookup \<tau> t) \<Longrightarrow> \<sigma> s = the (lookup \<tau> t s)"
  assumes beh: "\<And>n. t \<le> n \<Longrightarrow> lookup \<theta> n = 0"
  shows "beval t \<sigma> \<gamma> \<theta> exp = beval_world w t exp"
proof -
  have "state_of_world w t = \<sigma>"
    using state_of_world[OF assms(1) assms(2) assms(4)] by auto
  moreover have "event_of_world w t = \<gamma>"
  proof (cases "0 < t")
    case True
    fix s
    have "w s t = \<sigma> s"
      using `state_of_world w t = \<sigma>` unfolding state_of_world_def by auto
    moreover have "w s (t - 1) = signal_of2 False \<theta> s (t - 1)"
      unfolding assms(1) worldline_def using True by auto
    ultimately show ?thesis
      unfolding event_of_world_def assms(3)
      by (smt Collect_cong \<open>state_of_world w t = \<sigma>\<close> assms(1) True diff_less less_numeral_extra(3)
          state_of_world_def worldline_def zero_less_one)
  next
    case False
    hence "t = 0" by auto
    hence ev: "event_of_world w t = {s. w s 0 \<noteq> False}"
      unfolding event_of_world_def by auto
    have \<gamma>_def': "\<gamma> = {s. \<sigma> s \<noteq> signal_of2 False \<theta> s 0}"
      using `t = 0` gam by auto
    have "\<theta> = 0"
      using beh unfolding `t = 0` by (simp add: poly_mapping_eqI)
    hence "\<And>s. signal_of2 False \<theta> s 0 = False"
      using signal_of2_empty by metis
    hence "\<gamma> = {s. \<sigma> s \<noteq> False}"
      using \<gamma>_def' by auto
    moreover have "\<And>s.  w s 0 = \<sigma> s"
      using `state_of_world w t = \<sigma>` `t = 0` unfolding state_of_world_def by auto
    ultimately  have "\<gamma> = {s. w s 0 \<noteq> False}"
      by auto
    thus ?thesis  using ev by auto
  qed
  ultimately have " beval t (state_of_world w t) (event_of_world w t) (beh_of_world w t) exp =
                    beval t \<sigma> \<gamma> (beh_of_world w t) exp" by auto
  also have "... = beval t \<sigma> \<gamma> \<theta> exp"
    using beval_beh_of_world[OF assms(1) beh] by auto
  finally show ?thesis
    unfolding beval_world_def by auto
qed

lemma Bguarded_hoare_valid:
  assumes "\<Turnstile>\<^sub>t {\<lambda>a. P a \<and> beval_world a t g} s1 {Q}" and "\<Turnstile>\<^sub>t {\<lambda>a. P a \<and> \<not> beval_world a t g} s2 {Q}"
  shows "\<Turnstile>\<^sub>t {P} Bguarded g s1 s2 {Q}"
  unfolding seq_hoare_valid_def
proof (rule)+
  fix \<sigma> :: "'a state"
  fix \<tau> \<theta> \<tau>' :: "'a transaction"
  fix \<gamma> :: "'a event"
  fix w w' :: "'a worldline"
  assume "context_invariant t \<sigma> \<gamma> \<theta> \<tau> \<and> w = worldline t \<sigma> \<theta> \<tau> \<and> P w \<and>
          t , \<sigma> , \<gamma> , \<theta> \<turnstile> <Bguarded g s1 s2 , \<tau>> \<longrightarrow>\<^sub>s \<tau>' \<and> w' = worldline t \<sigma> \<theta> \<tau>'"
  hence s: "t , \<sigma> , \<gamma> , \<theta> \<turnstile> <Bguarded g s1 s2 , \<tau>> \<longrightarrow>\<^sub>s \<tau>'" and w: "w = worldline t \<sigma> \<theta> \<tau>"
    and c: "context_invariant t \<sigma> \<gamma> \<theta> \<tau>" and p: "P w" and w': "w' = worldline t \<sigma> \<theta> \<tau>'"
    by auto
  have "beval t \<sigma> \<gamma> \<theta> g \<or> \<not> beval t \<sigma> \<gamma> \<theta> g"
    by auto
  moreover
  { assume "beval t \<sigma> \<gamma> \<theta> g "
    hence \<tau>'_def: "t , \<sigma> , \<gamma> , \<theta> \<turnstile> <s1 , \<tau>> \<longrightarrow>\<^sub>s \<tau>'"
      using s by auto
    have "beval_world w t g"
      using `beval t \<sigma> \<gamma> \<theta> g` beval_beval_world[OF w _ _ _ _] c unfolding context_invariant_def
      by auto
    with `P w` have " Q w'"
      using assms(1) c w \<tau>'_def w' unfolding seq_hoare_valid_def by auto }
  moreover
  { assume "\<not> beval t \<sigma> \<gamma> \<theta> g"
    hence \<tau>'_def: "t, \<sigma>, \<gamma>, \<theta> \<turnstile> <s2, \<tau>> \<longrightarrow>\<^sub>s \<tau>'"
      using s by auto
    have "\<not> beval_world w t g"
      using `\<not> beval t \<sigma> \<gamma> \<theta> g` beval_beval_world[OF w _ _ _ _] c unfolding context_invariant_def
      by auto
    with `P w` have "Q w'"
      using assms(2) c w \<tau>'_def w' unfolding seq_hoare_valid_def by auto }
  ultimately show "Q w'" by auto
qed

lemma Bassign_trans_sound:
  "\<turnstile>\<^sub>t {P} Bassign_trans sig exp dly {Q} \<Longrightarrow> \<Turnstile>\<^sub>t {P} Bassign_trans sig exp dly {Q}"
proof -
  assume "\<turnstile>\<^sub>t {P} Bassign_trans sig exp dly {Q}"
  hence imp: "\<forall>w. P w \<longrightarrow> Q(w[sig, t + dly := beval_world w t exp])"
    by (auto dest!: BassignE)
  { fix \<sigma> :: "'a state"
    fix \<tau> \<tau>' \<theta> :: "'a transaction"
    fix w w' :: "'a worldline"
    fix \<gamma>
    assume "context_invariant t \<sigma> \<gamma> \<theta> \<tau>"
    assume "w = worldline t \<sigma> \<theta> \<tau>"
    assume "P w"
    assume "t, \<sigma>, \<gamma>, \<theta> \<turnstile> <Bassign_trans sig exp dly, \<tau>> \<longrightarrow>\<^sub>s \<tau>'"
    hence "\<tau>' = trans_post sig (beval t \<sigma> \<gamma> \<theta> exp) \<tau> (t + dly)"
      by auto
    moreover have "beval t \<sigma> \<gamma> \<theta> exp = beval_world w t exp"
      using `w = worldline t \<sigma> \<theta> \<tau>`  `context_invariant t \<sigma> \<gamma> \<theta> \<tau>`
      unfolding context_invariant_def by (simp add: beval_beval_world)
    ultimately have \<tau>'_def: "\<tau>' = trans_post sig (beval_world w t exp) \<tau> (t + dly)"
      by auto
    have "worldline t \<sigma> \<theta> \<tau>' = w[sig, t + dly := beval_world w t exp]"
    proof (rule ext, rule ext)
      fix s' t'
      have "t' < t \<or> t' \<ge> t" by auto
      moreover
      { assume "t' < t"
        hence 0: " worldline t \<sigma> \<theta> \<tau>' s' t' =  signal_of2 False \<theta> s' t'"
          unfolding worldline_def by auto
        have "t' < t + dly"
          using `t' < t` by auto
        hence "w[sig, t + dly := beval_world w t exp] s' t' = worldline t \<sigma> \<theta> \<tau> s' t'"
          unfolding `w = worldline t \<sigma> \<theta> \<tau>` worldline_upd_def by auto
        also have "... = signal_of2 False \<theta> s' t'"
          using `t' < t` unfolding worldline_def by auto
        finally have "w[sig, t + dly := beval_world w t exp] s' t' = signal_of2 False \<theta> s' t'"
          by auto
        hence "worldline t \<sigma> \<theta> \<tau>' s' t' = w[sig, t + dly := beval_world w t exp] s' t'"
          using 0 by auto }
      moreover
      { assume "t' \<ge> t"
        hence 0: "worldline t \<sigma> \<theta> \<tau>' s' t' = signal_of2 (\<sigma> s') \<tau>' s' t'"
          unfolding worldline_def by auto
        have "t' < t + dly \<or> t' \<ge> t + dly"
          by auto
        moreover
        { assume "t' < t + dly"
          have "w[sig, t + dly := beval_world w t exp] s' t' = worldline t \<sigma> \<theta> \<tau> s' t'"
            using `t' < t + dly` unfolding `w = worldline t \<sigma> \<theta> \<tau>` worldline_upd_def by auto
          also have "... = signal_of2 (\<sigma> s') \<tau> s' t'"
            using `t' \<ge> t` unfolding worldline_def by auto
          finally have 1: "w[sig, t + dly := beval_world w t exp] s' t' = signal_of2 (\<sigma> s') \<tau> s' t'"
            by auto

          have "worldline t \<sigma> \<theta> \<tau>' s' t' = signal_of2 (\<sigma> s') \<tau>' s' t'"
            using `t' \<ge> t` unfolding worldline_def by auto
          also have "... = signal_of2 (\<sigma> s') \<tau> s' t'"
            using signal_of_trans_post2[OF `t' < t + dly`] unfolding \<tau>'_def by metis
          also have "... = w[sig, t + dly := beval_world w t exp] s' t'"
            using 1 by auto
          finally have "worldline t \<sigma> \<theta> \<tau>' s' t' = w[sig, t + dly := beval_world w t exp] s' t'"
            by auto }
        moreover
        { assume "t' \<ge> t + dly"
          have "s' = sig \<or> s' \<noteq> sig" by auto
          moreover
          { assume "s' = sig"
            hence 2: "w[sig, t + dly := beval_world w t exp] s' t' = beval_world (worldline t \<sigma> \<theta> \<tau>) t exp"
              using `t' \<ge> t + dly` unfolding `w = worldline t \<sigma> \<theta> \<tau>` worldline_upd_def by auto
            have "worldline t \<sigma> \<theta> \<tau>' s' t' = signal_of2 (\<sigma> s') \<tau>' s' t'"
              using `t' \<ge> t` unfolding worldline_def by auto
            also have "... = beval_world (worldline t \<sigma> \<theta> \<tau>) t exp"
              using signal_of_trans_post3[OF `t + dly \<le> t'`, of "\<sigma> s'" "sig"] unfolding \<tau>'_def
              `w = worldline t \<sigma> \<theta> \<tau>` by (simp add: \<open>s' = sig\<close>)
            finally have "worldline t \<sigma> \<theta> \<tau>' s' t' = w[sig, t + dly := beval_world w t exp] s' t' "
              using 2 by auto }
          moreover
          { assume "s' \<noteq> sig"
            hence "sig \<noteq> s'" by auto
            hence "w[sig, t + dly := beval_world w t exp] s' t' = worldline t \<sigma> \<theta> \<tau> s' t'"
              unfolding `w = worldline t \<sigma> \<theta> \<tau>` worldline_upd_def  by auto
            also have "... = signal_of2 (\<sigma> s') \<tau> s' t'"
              using `t' \<ge> t` unfolding worldline_def by auto
            finally have 3: "w[sig, t + dly := beval_world w t exp] s' t' = signal_of2 (\<sigma> s') \<tau> s' t'"
              by auto
            have "worldline t \<sigma> \<theta> \<tau>' s' t' = signal_of2 (\<sigma> s') \<tau>' s' t'"
              using `t' \<ge> t` unfolding worldline_def by auto
            also have "... = signal_of2 (\<sigma> s') \<tau> s' t'"
              unfolding \<tau>'_def using signal_of_trans_post[OF `sig \<noteq> s'`] by metis
            also have "... = w[sig, t + dly := beval_world w t exp] s' t'"
              using 3 by auto
            finally have "worldline t \<sigma> \<theta> \<tau>' s' t' = w[sig, t + dly := beval_world w t exp] s' t' "
              by auto }
          ultimately have "worldline t \<sigma> \<theta> \<tau>' s' t' = w[sig, t + dly := beval_world w t exp] s' t' "
            by auto }
        ultimately have "worldline t \<sigma> \<theta> \<tau>' s' t' = w[sig, t + dly := beval_world w t exp] s' t' "
          by auto }
      ultimately show "worldline t \<sigma> \<theta> \<tau>' s' t' = w[sig, t + dly := beval_world w t exp] s' t'"
        by auto
    qed
    with imp and `P w` have "Q(w[sig, t + dly := beval_world w t exp])"
      by auto
    assume "w' = worldline t \<sigma> \<theta> \<tau>'"
    hence "Q w'"
      using `Q(w[sig, t + dly := beval_world w t exp])` `worldline t \<sigma> \<theta> \<tau>' = w[sig, t + dly := beval_world w t exp]`
      by auto }
  thus " \<Turnstile>\<^sub>t {P} Bassign_trans sig exp dly {Q}"
    unfolding seq_hoare_valid_def by auto
qed

lemma Bassign_inert_sound:
  assumes "0 < dly"
  shows "\<turnstile>\<^sub>t {P} Bassign_inert sig exp dly {Q} \<Longrightarrow> \<Turnstile>\<^sub>t {P} Bassign_inert sig exp dly {Q}"
proof -
  assume "\<turnstile>\<^sub>t {P} Bassign_inert sig exp dly {Q}"
  hence imp: "\<forall>w. P w \<longrightarrow> Q(w[sig, t + dly, t := beval_world w t exp])"
    by (auto dest!: Bassign_inertE)
  { fix \<sigma> :: "'a state"
    fix \<tau> \<tau>' \<theta> :: "'a transaction"
    fix w w' :: "'a worldline"
    fix \<gamma>
    assume c: "context_invariant t \<sigma> \<gamma> \<theta> \<tau>"
    assume "w = worldline t \<sigma> \<theta> \<tau>"
    assume "P w"
    assume ex: "t, \<sigma>, \<gamma>, \<theta> \<turnstile> <Bassign_inert sig exp dly, \<tau>> \<longrightarrow>\<^sub>s \<tau>'"
    hence "\<tau>' = inr_post sig (beval t \<sigma> \<gamma> \<theta> exp) (\<sigma> sig) \<tau> t dly"
      by auto
    moreover have "beval t \<sigma> \<gamma> \<theta> exp = beval_world w t exp"
      using `w = worldline t \<sigma> \<theta> \<tau>`  `context_invariant t \<sigma> \<gamma> \<theta> \<tau>`
      unfolding context_invariant_def by (simp add: beval_beval_world)
    ultimately have \<tau>'_def: "\<tau>' = inr_post sig (beval_world w t exp) (\<sigma> sig) \<tau> t dly"
      by auto
    have "\<And>n. n < t \<Longrightarrow> lookup \<tau> n = 0"
      using `context_invariant t \<sigma> \<gamma> \<theta> \<tau>` unfolding context_invariant_def by auto
    hence "\<And>n. n < t \<Longrightarrow> lookup \<tau>' n = 0"
      unfolding \<tau>'_def using inr_post_preserve_trans_removal by metis
    have nn: "nonneg_delay (Bassign_inert sig exp dly)"
      using `0 < dly` by auto
    have "context_invariant t \<sigma> \<gamma> \<theta> \<tau>'"
      using b_seq_exec_preserves_context_invariant[OF c ex nn] by auto
    hence asm: "\<forall>s. s \<in> dom (get_trans \<tau>' t) \<longrightarrow> \<sigma> s = the (get_trans \<tau>' t s)"
      unfolding context_invariant_def by auto
    hence asm': "\<forall>s. s \<in> dom (get_trans \<tau> t) \<longrightarrow> \<sigma> s = the (get_trans \<tau> t s)"
      using `context_invariant t \<sigma> \<gamma> \<theta> \<tau>` unfolding context_invariant_def by auto
    have "worldline t \<sigma> \<theta> \<tau>' = w[sig, t + dly, t := beval_world w t exp]"
    proof (rule ext, rule ext)
      fix s' t'
      have "s' \<noteq> sig \<or> t' < t \<or> s' = sig \<and> t \<le> t'"
        by auto
      moreover
      { assume "s' \<noteq> sig \<or> t' < t"
        moreover
        { assume "t' < t"
          hence 0: " worldline t \<sigma> \<theta> \<tau>' s' t' =  signal_of2 False \<theta> s' t'"
            unfolding worldline_def by auto
          have "t' < t + dly"
            using `t' < t` by auto
          hence "w[sig, t + dly, t := beval_world w t exp] s' t' = worldline t \<sigma> \<theta> \<tau> s' t'"
            unfolding `w = worldline t \<sigma> \<theta> \<tau>` worldline_inert_upd_def  by (simp add: \<open>t' < t\<close>)
          also have "... = signal_of2 False \<theta> s' t'"
            using `t' < t` unfolding worldline_def by auto
          finally have "w[sig, t + dly, t := beval_world w t exp] s' t' = signal_of2 False \<theta> s' t'"
            by auto
          hence "worldline t \<sigma> \<theta> \<tau>' s' t' = w[sig, t + dly, t := beval_world w t exp] s' t'"
            using 0 by auto }
        moreover
        { assume "s' \<noteq> sig"
          hence "w[sig, t + dly, t := beval_world w t exp] s' t' = worldline t \<sigma> \<theta> \<tau> s' t'"
            unfolding worldline_inert_upd_def `w = worldline t \<sigma> \<theta> \<tau>` by auto
          also have "... = worldline t \<sigma> \<theta> \<tau>' s' t'"
          proof -
            have "\<And>n. lookup (to_transaction2 \<tau> s') n = lookup (to_transaction2 \<tau>' s') n"
              using `s' \<noteq> sig` unfolding \<tau>'_def inr_post_def apply transfer' unfolding to_trans_raw2_def
              trans_post_raw_def  by (simp add: purge_raw_does_not_affect_other_sig)
            hence "signal_of2 (\<sigma> s') \<tau> s' t' = signal_of2 (\<sigma> s') \<tau>'  s' t'"
              using signal_of2_lookup_sig_same  by metis
            thus ?thesis
              unfolding worldline_def by auto
          qed
          finally have "worldline t \<sigma> \<theta> \<tau>' s' t' = w[sig, t + dly, t := beval_world w t exp] s' t'"
            by auto }
        ultimately have "worldline t \<sigma> \<theta> \<tau>' s' t' = w[sig, t + dly, t := beval_world w t exp] s' t'"
          by auto }
      moreover
      { assume "s' = sig \<and> t \<le> t'"
        hence "t + dly \<le> t' \<or> t' < t + dly" and "s' = sig" and "t \<le> t'"
          by auto
        moreover
        { assume "t + dly \<le> t'"
          hence 2: "w[sig, t + dly, t := beval_world w t exp] s' t' = beval_world (worldline t \<sigma> \<theta> \<tau>) t exp"
              using `s' = sig` unfolding `w = worldline t \<sigma> \<theta> \<tau>` worldline_inert_upd_def by auto
          have "worldline t \<sigma> \<theta> \<tau>' s' t' = signal_of2 (\<sigma> s') \<tau>' s' t'"
            using `t' \<ge> t` unfolding worldline_def by auto
          also have "... = beval_world (worldline t \<sigma> \<theta> \<tau>) t exp"
            using signal_of_inr_post[OF `t + dly \<le> t'`, of "\<sigma> s'" "sig"] unfolding \<tau>'_def
            `w = worldline t \<sigma> \<theta> \<tau>` by (simp add: \<open>s' = sig \<and> t \<le> t'\<close>)
          finally have "worldline t \<sigma> \<theta> \<tau>' s' t' = w[sig, t + dly, t := beval_world w t exp] s' t' "
            using 2 by auto }
        moreover
        { assume "t' < t + dly"
          hence "w[sig, t + dly, t := beval_world w t exp] s' t' = w sig t"
            unfolding worldline_inert_upd_def using `s' = sig`  using \<open>s' = sig \<and> t \<le> t'\<close> by auto
          also have "... = signal_of2 (\<sigma> sig) \<tau> sig t"
            unfolding `w = worldline t \<sigma> \<theta> \<tau>` worldline_def by auto
          also have "... = \<sigma> sig"
          proof (cases "lookup \<tau> t sig = None")
            case True
            have "\<And>k. k \<in>dom (lookup (to_transaction2 \<tau> sig)) \<Longrightarrow> t < k"
            proof (rule ccontr)
              fix k
              assume in_dom: "k \<in>dom (lookup (to_transaction2 \<tau> sig))"
              assume "\<not> t < k" hence "k \<le> t" by auto
              hence "lookup \<tau> k sig = None"
                using `\<And>n. n < t \<Longrightarrow> lookup \<tau> n = 0` True  by (metis dual_order.antisym leI zero_map)
              hence "k \<notin> dom (lookup (to_transaction2 \<tau> sig))"
                apply transfer' unfolding to_trans_raw2_def by auto
              with in_dom show "False" by auto
            qed
            hence "inf_time (to_transaction2 \<tau>) sig t = None"
              by (simp add: inf_time_noneI)
            then show ?thesis
              unfolding to_signal2_def comp_def by auto
          next
            case False
            hence "lookup \<tau> t sig = Some (\<sigma> sig)"
              using asm'  by (simp add: domIff)
            with lookup_some_signal_of2' show ?thesis
              by fastforce
          qed
          finally have l: "w[sig, t + dly, t := beval_world w t exp] s' t' = \<sigma> sig"
            by auto

          have "worldline t \<sigma> \<theta> \<tau>' s' t' = signal_of2 (\<sigma> s') \<tau>' s' t'"
            unfolding worldline_def using `s' = sig \<and> t \<le> t'` by auto
          also have "... = \<sigma> s'"
            using signal_of_inr_post2[OF `t \<le> t'` `t' < t + dly` `\<And>n. n < t \<Longrightarrow> lookup \<tau> n = 0` asm', of "s'"]
            unfolding \<tau>'_def using `s' = sig` by auto
          finally have "worldline t \<sigma> \<theta> \<tau>' s' t' = \<sigma> s'"
            by auto
          with l have "worldline t \<sigma> \<theta> \<tau>' s' t' = w[sig, t + dly, t := beval_world w t exp] s' t' "
            using `s' = sig` by auto }
        ultimately have "worldline t \<sigma> \<theta> \<tau>' s' t' = w[sig, t + dly, t := beval_world w t exp] s' t' "
          by auto }
      ultimately show "worldline t \<sigma> \<theta> \<tau>' s' t' = w[sig, t + dly, t := beval_world w t exp] s' t' "
        by auto
    qed
    with imp and `P w` have "Q(w[sig, t + dly, t := beval_world w t exp])"
      by auto
    assume "w' = worldline t \<sigma> \<theta> \<tau>'"
    hence "Q w'"
      using `Q(w[sig, t + dly, t := beval_world w t exp])` `worldline t \<sigma> \<theta> \<tau>' = w[sig, t + dly, t:= beval_world w t exp]`
      by auto }
  thus " \<Turnstile>\<^sub>t {P} Bassign_inert sig exp dly {Q}"
    unfolding seq_hoare_valid_def by auto
qed

lemma soundness:
  assumes "\<turnstile>\<^sub>t {P} s {R}"
  assumes "nonneg_delay s"
  shows "\<Turnstile>\<^sub>t {P} s {R}"
  using assms
proof (induction rule:seq_hoare.induct)
  case (AssignI t P sig dly exp)
  hence "0 < dly" by auto
  then show ?case
    using Bassign_inert_sound[OF `0 < dly`]  using seq_hoare.AssignI by fastforce
next
  case (Conseq P' P t s Q Q')
  then show ?case  by (auto simp add: seq_hoare_valid_def)
qed (auto simp add: Bnull_sound Bassign_trans_sound Bcomp_hoare_valid Bguarded_hoare_valid)

end