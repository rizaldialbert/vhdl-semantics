(*
 * Copyright 2019, NTU
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 *  Author: Albert Rizaldi, NTU Singapore
 *)

theory VHDL_Hoare_Complete
  imports VHDL_Hoare
          "HOL-Library.Poly_Mapping"
begin

subsection \<open>A sound and complete Hoare logic for VHDL's sequential statements\<close>

definition worldline_upd2 ::
  "nat \<times> 'signal worldline_init \<Rightarrow> 'signal \<Rightarrow> nat \<Rightarrow> val \<Rightarrow> nat \<times> 'signal worldline_init" ("_[ _, _ :=\<^sub>2 _]")
  where "worldline_upd2 \<equiv> \<lambda>tw sig dly val. (fst tw, worldline_upd (snd tw) sig (fst tw + dly) val)"

abbreviation wline_of where "wline_of (tw :: nat \<times> 'signal worldline_init) \<equiv> (snd o snd) tw"

lemma worldline_upd2_before_dly:
  fixes tw val dly sig
  defines "tw' \<equiv> tw[sig, dly :=\<^sub>2 val]"
  shows "\<And>s i. i < fst tw + dly \<Longrightarrow> wline_of tw' s i = wline_of tw s i"
  unfolding tw'_def worldline_upd2_def worldline_upd_def by auto

lemma worldline_upd2_at_dly:
  fixes tw val dly sig
  defines "tw' \<equiv> tw[sig, dly :=\<^sub>2 val]"
  shows "wline_of tw' sig (fst tw + dly) = val"
  unfolding tw'_def worldline_upd2_def worldline_upd_def by auto

lemma worldline_upd2_at_dly_nonsig:
  fixes tw val dly sig
  defines "tw' \<equiv> tw[sig, dly :=\<^sub>2 val]"
  shows "s \<noteq> sig \<Longrightarrow> wline_of tw' s (fst tw + dly) = wline_of tw s (fst tw + dly)"
  unfolding tw'_def worldline_upd2_def worldline_upd_def by auto

definition worldline_inert_upd2 ::
  "nat \<times> 'signal worldline_init \<Rightarrow> 'signal \<Rightarrow> nat \<Rightarrow> val \<Rightarrow> nat \<times> 'signal worldline_init" ("_\<lbrakk> _, _ :=\<^sub>2 _\<rbrakk>")
  where "worldline_inert_upd2 \<equiv> \<lambda>tw sig dly v. (fst tw, worldline_inert_upd (snd tw) sig (fst tw) dly v)"

definition beval_world_raw2 :: "nat \<times> 'signal worldline_init \<Rightarrow> 'signal bexp \<Rightarrow> val \<Rightarrow> bool" where
  "beval_world_raw2 \<equiv> \<lambda>tw exp. beval_world_raw (snd tw) (fst tw) exp"

lemma beval_world_raw2_Bsig:
  "beval_world_raw2 tw (Bsig s) (wline_of tw s (fst tw))"
  unfolding beval_world_raw2_def
  by (auto intro!: beval_world_raw.intros beval_raw.intros simp add: state_of_world_def)

type_synonym 'signal assn2 = "nat \<times> 'signal worldline_init \<Rightarrow> bool"

inductive
  seq_hoare2 :: "'signal assn2 \<Rightarrow> 'signal seq_stmt \<Rightarrow> 'signal assn2 \<Rightarrow> bool" ("\<turnstile> ([(1_)]/ (_)/ [(1_)])" 50)
  where
Null2: "\<turnstile> [P] Bnull [P]"

| Assign2: "\<turnstile> [\<lambda>tw. (\<forall>x. beval_world_raw2 tw exp x \<longrightarrow> P(  tw[sig, dly :=\<^sub>2 x] )) ] Bassign_trans sig exp dly [P]"

| AssignI2: "\<turnstile> [\<lambda>tw. (\<forall>x. beval_world_raw2 tw exp x \<longrightarrow> P( tw\<lbrakk>sig, dly :=\<^sub>2 x\<rbrakk>))] Bassign_inert sig exp dly [P]"

| Comp2: "\<lbrakk> \<turnstile> [P] s1 [Q]; \<turnstile> [Q] s2 [R]\<rbrakk> \<Longrightarrow> \<turnstile> [P] Bcomp s1 s2 [R]"

| If2: "\<lbrakk>\<turnstile> [\<lambda>tw. P tw \<and> beval_world_raw2 tw g (Bv True)] s1 [Q];
         \<turnstile> [\<lambda>tw. P tw \<and> beval_world_raw2 tw g (Bv False)] s2 [Q]\<rbrakk>
        \<Longrightarrow>  \<turnstile> [P] Bguarded g s1 s2 [Q]"

| Conseq2: "\<lbrakk>\<forall>tw. P' tw \<longrightarrow> P tw; \<turnstile> [P] s [Q]; \<forall>tw. Q tw \<longrightarrow> Q' tw\<rbrakk> \<Longrightarrow> \<turnstile> [P'] s [Q']"

| Conj: "\<turnstile> [P] s [Q1] \<Longrightarrow> \<turnstile> [P] s [Q2] \<Longrightarrow> \<turnstile> [P] s [\<lambda>tw. Q1 tw \<and> Q2 tw]"

| Bcase_empty_choices2: "\<turnstile> [P] Bcase exp [] [P]"

| Bcase_others2: "\<turnstile> [P] ss [Q] \<Longrightarrow> \<turnstile> [P] Bcase exp ((Others, ss) # choices) [Q]"

| Bcase_if2: "\<turnstile> [\<lambda>tw. P tw \<and> (\<exists>x. beval_world_raw2 tw exp x \<and> beval_world_raw2 tw exp' x)] ss [Q]
  \<Longrightarrow> \<turnstile> [\<lambda>tw. P tw \<and> (\<exists>x x'. beval_world_raw2 tw exp x \<and> beval_world_raw2 tw exp' x' \<and> x \<noteq> x')] Bcase exp choices [Q]
  \<Longrightarrow> \<turnstile> [P] Bcase exp ( (Explicit exp', ss) # choices) [Q]"

text \<open>Derived rules\<close>

lemma strengthen_precondition:
  "\<turnstile> [P] ss [Q] \<Longrightarrow> \<turnstile> [\<lambda>tw. P tw \<and> P' tw] ss [Q]"
  by (rule Conseq2[where Q="Q" and P="P"]) auto

lemma strengthen_precondition2:
  "\<turnstile> [P'] ss [Q] \<Longrightarrow> \<turnstile> [\<lambda>tw. P tw \<and> P' tw] ss [Q]"
  by (rule Conseq2[where Q="Q" and P="P'"]) auto

lemma weaken_postcondition:
  "\<turnstile> [P] ss [\<lambda>tw. Q1 tw \<and> Q2 tw] \<Longrightarrow> \<turnstile> [P] ss [Q1]"
  by (rule Conseq2) auto

lemma compositional_conj:
  assumes "\<turnstile> [P1] ss [Q1]" and "\<turnstile> [P2] ss [Q2]"
  shows "\<turnstile> [\<lambda>tw. P1 tw \<and> P2 tw] ss [\<lambda>tw. Q1 tw \<and> Q2 tw]"
  apply(rule Conj)
   apply(rule Conseq2[where P="P1" and Q="Q1"])
     apply simp
    apply(rule assms(1))
   apply simp
  apply(rule Conseq2[where P="P2" and Q="Q2"])
    apply simp
   apply (rule assms(2))
  apply simp
  done

inductive_cases seq_hoare2_ic: "\<turnstile> [P] s [Q]"

lemma Assign2_altI:
  "\<forall>tw x. P tw \<and> beval_world_raw2 tw exp x \<longrightarrow> Q(tw[sig, dly :=\<^sub>2 x]) \<Longrightarrow> \<turnstile> [P] Bassign_trans sig exp dly [Q]"
  apply (rule Conseq2[where Q="Q", rotated 1])
    apply (rule Assign2)
   apply simp
  apply simp
  done

lemma AssignI2_altI:
  "\<forall>tw x. P tw \<and> beval_world_raw2 tw exp x \<longrightarrow> Q(tw\<lbrakk>sig, dly :=\<^sub>2 x\<rbrakk>) \<Longrightarrow> \<turnstile> [P] Bassign_inert sig exp dly [Q]"
  apply (rule Conseq2[where Q="Q", rotated 1])
    apply (rule AssignI2)
   apply simp
  apply simp
  done

lemma BnullE_hoare2:
  assumes "\<turnstile> [P] s [Q]"
  assumes "s = Bnull"
  shows "\<forall>tw. P tw \<longrightarrow> Q tw"
  using assms
  by (induction rule:seq_hoare2.induct, auto)

lemma BnullE'_hoare2:
  "\<turnstile> [P] Bnull [Q] \<Longrightarrow> \<forall>tw. P tw \<longrightarrow> Q tw"
  using BnullE_hoare2 by blast

lemma BassignE_hoare2:
  assumes "\<turnstile> [P] s [Q]"
  assumes "s = Bassign_trans sig exp dly"
  shows "\<forall>tw x. P tw \<and> beval_world_raw2 tw exp x \<longrightarrow> Q(tw[sig, dly :=\<^sub>2 x])"
  using assms
proof (induction rule: seq_hoare2.induct)
  case (Conseq2 P' P s Q Q')
  then show ?case by blast
next
  case (Conj P s Q1 Q2)
  then show ?case
    by (metis beval_world_raw2_def beval_world_raw_deterministic)
qed (auto)

lemma Bassign_inertE_hoare2:
  assumes "\<turnstile> [P] s [Q]"
  assumes "s = Bassign_inert sig exp dly"
  shows "\<forall>tw x. P tw \<and> beval_world_raw2 tw exp x \<longrightarrow> Q(tw \<lbrakk> sig, dly :=\<^sub>2 x\<rbrakk>)"
  using assms
proof (induction rule: seq_hoare2.induct)
  case (Conseq2 P' P s Q Q')
  then show ?case by blast
next
  case (Conj P s Q1 Q2)
  then show ?case
    by (metis beval_world_raw2_def beval_world_raw_deterministic)
qed auto

lemma BcompE_hoare2:
  assumes "\<turnstile> [P] s [R]"
  assumes "s = Bcomp s1 s2"
  shows "\<exists>Q. \<turnstile> [P] s1 [Q] \<and> \<turnstile> [Q] s2 [R]"
  using assms
proof (induction rule:seq_hoare2.induct)
  case (Conseq2 P' P s Q Q')
  then show ?case
    using seq_hoare2.Conseq2 by blast
next
  case (Conj P s Q1 Q2)
  then obtain Q1' Q2' where " \<turnstile> [P] s1 [Q1']" and "\<turnstile> [Q1'] s2 [Q1]" and " \<turnstile> [P] s1 [Q2']" and "\<turnstile> [Q2'] s2 [Q2]"
    by auto
  hence "\<turnstile> [P] s1 [\<lambda>tw. Q1' tw \<and> Q2' tw]"
    using seq_hoare2.Conj by auto
  moreover have "\<turnstile> [\<lambda>tw. Q1' tw \<and> Q2' tw] s2 [\<lambda>tw. Q1 tw \<and> Q2 tw]"
    by (simp add: compositional_conj \<open>\<turnstile> [Q1'] s2 [Q1]\<close> \<open>\<turnstile> [Q2'] s2 [Q2]\<close>)
  ultimately have "\<turnstile> [P] s1 [\<lambda>tw. Q1' tw \<and> Q2' tw] \<and> \<turnstile> [\<lambda>tw. Q1' tw \<and> Q2' tw] s2 [\<lambda>tw. Q1 tw \<and> Q2 tw]"
    by auto
  then show ?case
    by (auto)
qed (auto simp add: Conseq2)

lemmas [simp] = seq_hoare2.Null2 seq_hoare2.Assign2 seq_hoare2.Comp2 seq_hoare2.If2
                seq_hoare2.Bcase_empty_choices2 seq_hoare2.Bcase_others2 seq_hoare2.Bcase_if2
lemmas [intro!] = seq_hoare2.Null2 seq_hoare2.Assign2 seq_hoare2.Comp2 seq_hoare2.If2
                seq_hoare2.Bcase_empty_choices2 seq_hoare2.Bcase_others2 seq_hoare2.Bcase_if2

lemma strengthen_pre_hoare2:
  assumes "\<forall>tw. P' tw \<longrightarrow> P tw" and "\<turnstile> [P] s [Q]"
  shows "\<turnstile> [P'] s [Q]"
  using assms by (blast intro: Conseq2)

lemma weaken_post_hoare2:
  assumes "\<forall>tw. Q tw \<longrightarrow> Q' tw" and "\<turnstile> [P] s [Q]"
  shows "\<turnstile> [P] s [Q']"
  using assms by (blast intro: Conseq2)

lemma Assign'_hoare2:
  assumes "\<forall>tw x. P tw \<and> beval_world_raw2 tw exp x \<longrightarrow> Q (worldline_upd2 tw sig dly x)"
  shows "\<turnstile> [P] Bassign_trans sig exp dly [Q]"
  using assms
  by (simp add: Assign2_altI)

subsubsection \<open>Validity of Hoare proof rules\<close>

definition worldline2 ::
  "nat \<Rightarrow> 'signal state \<Rightarrow> 'signal trans_raw \<Rightarrow> 'signal state \<Rightarrow> 'signal trans_raw \<Rightarrow> nat \<times> 'signal worldline_init"
  where "worldline2 \<equiv> \<lambda>t \<sigma> \<theta> def \<tau>. (t, worldline_raw t \<sigma> \<theta> def \<tau>)"

definition destruct_worldline ::
  "nat \<times> 'signal worldline_init \<Rightarrow> (nat \<times> 'signal state \<times> 'signal event \<times> 'signal trans_raw \<times> 'signal state \<times> 'signal trans_raw)"
  where
  "destruct_worldline tw = (let  t = fst tw; w = snd tw; def = fst w;
                                 \<sigma> = (\<lambda>s. snd w s t);
                                 \<theta> = derivative_hist_raw w t;
                                 \<gamma> = {s. \<sigma> s \<noteq> signal_of (def s) \<theta> s (t - 1)};
                                 \<tau> = derivative_raw w t
                             in (t, \<sigma>, \<gamma>, \<theta>, def, \<tau>))"

lemma destruct_worldline_trans_zero_upto_now:
  assumes "destruct_worldline tw = (t, \<sigma>, \<gamma>, \<theta>, def, \<tau>)"
  shows "\<And>n. n \<le> t \<Longrightarrow> \<tau> n = 0"
proof -
  have "\<tau> = derivative_raw (snd tw) (fst tw)" and "fst tw = t"
    using assms unfolding destruct_worldline_def Let_def by auto
  hence "\<And>n. n \<le> t \<Longrightarrow> \<tau> n = Map.empty"
    unfolding derivative_raw_def  `fst tw = t` by auto
  thus "\<And>n. n \<le> t \<Longrightarrow> \<tau> n = 0"
    unfolding zero_fun_def zero_option_def by auto
qed

text \<open>One might concern about the event @{term "\<gamma> :: 'signal event"} obtained from the destruction
@{term "destruct_worldline tw"} above. What happens if @{term "t = 0"}? This is a valid concern
since we have the expression @{term "t - 1"} in the definition of @{term "\<gamma>"} above.

Note that, we impose the requirement of @{term "context_invariant"} here. When this is the case,
history @{term "\<theta> :: 'signal trans_raw"} is empty when @{term "t = 0"}. Hence the expression
@{term "signal_of (def s) \<theta> s (t - 1)"} is equal to @{term "signal_of (def s) 0 s 0"} and,
subsequently, equals to @{term "False"}. Hence, when @{term "t = 0"}, the @{term "\<gamma>"} enumerates the
signals which are different with the default value @{term "Bv False :: val"}.\<close>

lemma destruct_worldline_no_trans_at_t:
  "destruct_worldline tw = (t, \<sigma>, \<gamma>, \<theta>, def, \<tau>) \<Longrightarrow> \<tau> t = 0"
proof -
  assume "destruct_worldline tw = (t, \<sigma>, \<gamma>, \<theta>, def, \<tau>)"
  hence "\<tau> = derivative_raw (snd tw) (fst tw)" and "fst tw = t"
    unfolding destruct_worldline_def Let_def by auto
  thus ?thesis
    by (auto simp add: derivative_raw_def zero_fun_def zero_option_def)
qed

lemma fst_destruct_worldline:
  "fst (destruct_worldline tw) = fst tw"
  unfolding destruct_worldline_def Let_def by auto

lemma destruct_worldline_exist:
  "\<exists>t \<sigma> \<gamma> \<theta> def \<tau>. destruct_worldline tw = (t, \<sigma>, \<gamma>, \<theta>, def, \<tau>)"
  unfolding destruct_worldline_def Let_def by auto

lemma worldline2_constructible:
  fixes tw :: "nat \<times> 'signal worldline_init"
  assumes "destruct_worldline tw = (t, \<sigma>, \<gamma>, \<theta>, def, \<tau>)"
  shows "tw = worldline2 t \<sigma> \<theta> def \<tau> \<and> context_invariant t \<sigma> \<gamma> \<theta> def \<tau>"
proof -
  let ?w = "snd tw"
  have **:
      "(fst tw,
        \<lambda>s. snd ?w s (fst tw),
        {s. snd ?w s (fst tw) \<noteq> signal_of (fst ?w s) (derivative_hist_raw (snd tw) (fst tw)) s (fst tw - 1)},
        derivative_hist_raw (snd tw) (fst tw),
        fst ?w,
        derivative_raw (snd tw) (fst tw)) =
        (t, \<sigma>, \<gamma>, \<theta>, def, \<tau>)"
    using assms unfolding destruct_worldline_def Let_def by auto
  hence \<sigma>_def: "\<sigma> = (\<lambda>s. snd ?w s t)" and
        \<gamma>_def: "\<gamma> = {s. snd ?w s t \<noteq> signal_of (def s) (derivative_hist_raw (snd tw) (fst tw)) s (fst tw - 1)}" and
        \<theta>_def: "\<theta> = derivative_hist_raw ?w t" and
        def_def: "def = fst ?w" and
        "fst tw = t"
    by auto
  have \<tau>_def: "\<tau> = derivative_raw ?w t"
    using ** by auto
  have "?w = worldline_raw t \<sigma> \<theta> def \<tau>"
  proof (rule, rule_tac[2] ext, rule_tac[2] ext)
    fix s' t'
    have "snd ?w s' t = \<sigma> s'"
      unfolding \<sigma>_def by auto
    have "t' < t \<or> t \<le> t'" by auto
    moreover
    { assume "t' < t"
      hence "snd (worldline_raw t \<sigma> \<theta> def \<tau>) s' t' =  signal_of (def s') \<theta> s' t'"
        unfolding worldline_raw_def by auto
      also have "... = snd ?w s' t'"
        using signal_of_derivative_hist_raw[OF `t' < t`, where w="?w"] unfolding \<theta>_def
        using def_def by blast
      finally have "snd ?w s' t' = snd (worldline_raw t \<sigma> \<theta> def \<tau>) s' t'"
        by auto }
    moreover
    { assume "t \<le> t'"
      hence "snd (worldline_raw t \<sigma> \<theta> def \<tau>) s' t' = signal_of (\<sigma> s') \<tau> s' t'"
        unfolding worldline_raw_def by auto
      also have "... = snd ?w s' t'"
        unfolding \<tau>_def using `snd ?w s' t = \<sigma> s'` by (metis \<open>t \<le> t'\<close> signal_of_derivative_raw)
      finally have "snd ?w s' t' = snd (worldline_raw t \<sigma> \<theta> def \<tau>) s' t'"
        by auto }
    ultimately show "snd ?w s' t' = snd (worldline_raw t \<sigma> \<theta> def \<tau>) s' t'"
      by auto
  qed (simp add: def_def worldline_raw_def)
  have "\<forall>n. t \<le> n \<longrightarrow> \<theta> n = 0"
    unfolding \<theta>_def by (auto simp add: derivative_hist_raw_def zero_fun_def zero_option_def)
  moreover have "\<forall>n. n \<le> t \<longrightarrow> \<tau> n = 0"
    unfolding \<tau>_def by (auto simp add: derivative_raw_def zero_fun_def zero_option_def)
  ultimately have "context_invariant t \<sigma> \<gamma> \<theta> def \<tau>"
    unfolding \<gamma>_def context_invariant_def \<sigma>_def \<theta>_def `fst tw = t` by auto
  thus "  tw = worldline2 t \<sigma> \<theta> def \<tau> \<and> context_invariant t \<sigma> \<gamma> \<theta> def \<tau>"
    using `?w = worldline_raw t \<sigma> \<theta> def \<tau>` `fst tw = t` surjective_pairing[of "tw"]
    by (metis worldline2_def)
qed

lemma worldline2_constructible':
  fixes tw :: "nat \<times> 'signal worldline_init"
  shows "\<exists>t \<sigma> \<gamma> \<theta> def \<tau>. tw = worldline2 t \<sigma> \<theta> def \<tau> \<and> context_invariant t \<sigma> \<gamma> \<theta> def \<tau>"
  using destruct_worldline_exist worldline2_constructible by blast

lemma state_worldline2:
  assumes "\<forall>n. n \<le> t \<longrightarrow>  \<tau> n = 0"
  assumes "\<forall>n. t \<le> n \<longrightarrow>  \<theta> n = 0"
  shows "(\<lambda>s. wline_of (worldline2 t \<sigma> \<theta> def \<tau>) s t) = \<sigma>"
  using assms
proof (intro ext)
  fix s
  have " \<tau> t s = 0"
    using assms(1) by (auto simp add: zero_fun_def )
  have "\<forall>k\<in>dom (to_trans_raw_sig \<tau> s). t < k"
  proof (rule ccontr)
    assume "\<not> (\<forall>k\<in>dom (to_trans_raw_sig \<tau> s). t < k)"
    then obtain k where k_dom: "k \<in> dom (to_trans_raw_sig \<tau> s)" and "k \<le> t"
      using leI by blast
    have " \<tau> k s = 0"
      using `\<forall>n. n \<le> t \<longrightarrow>  \<tau> n = 0` ` \<tau> t s = 0` `k \<le> t`
      by (metis zero_fun_def)
    moreover have " \<tau> k s \<noteq> 0"
      using k_dom unfolding domIff zero_option_def  unfolding to_trans_raw_sig_def
      by auto
    ultimately show "False"
      by auto
  qed
  hence "Femto_VHDL_raw.inf_time (to_trans_raw_sig \<tau>) s t = None"
    by (auto simp add: inf_time_none_iff)
  hence "signal_of (\<sigma> s) \<tau> s t = \<sigma> s"
    unfolding Femto_VHDL_raw.to_signal_def comp_def by auto
  hence "snd (worldline_raw t \<sigma> \<theta> def \<tau>) s t = \<sigma> s"
    unfolding worldline_raw_def by auto
  thus "wline_of (worldline2 t \<sigma> \<theta> def \<tau>) s t = \<sigma> s"
    by (simp add: worldline2_def)
qed

lemma hist_of_worldline:
  assumes "\<forall>n. n \<le> t \<longrightarrow>  \<tau> n = 0"
  assumes "\<forall>n. t \<le> n \<longrightarrow>  \<theta> n = 0"
  shows "\<And>k. signal_of (def s) (derivative_hist_raw (snd (worldline2 t \<sigma> \<theta> def \<tau>)) t) s k = signal_of (def s) \<theta> s k"
  using assms
proof -
  fix k
  have *: "signal_of (def s) (derivative_hist_raw (snd (worldline2 t \<sigma> \<theta> def \<tau>)) t) s k  =
           signal_of (def s) (derivative_hist_raw (worldline_raw t \<sigma> \<theta> def \<tau>) t) s k"
    unfolding worldline2_def by auto
  have "\<theta> t = 0"
    using assms by auto
  have "k < t \<or> t \<le> k"
    by auto
  moreover
  { assume "k < t"
    have "signal_of (def s) (derivative_hist_raw (worldline_raw t \<sigma> \<theta> def \<tau>) t) s k = snd (worldline_raw t \<sigma> \<theta> def \<tau>) s k"
      using signal_of_derivative_hist_raw[OF `k < t`]  by (smt fst_conv worldline_raw_def)
    also have "... = signal_of (def s) \<theta> s k"
      using `k < t` unfolding worldline_raw_def by auto
    finally have "signal_of (def s) (derivative_hist_raw (snd (worldline2 t \<sigma> \<theta> def \<tau>)) t) s k  = signal_of (def s) \<theta> s k "
      using * by auto }
  moreover
  { assume "t \<le> k"
    hence "t < k \<or> t = k" by auto
    moreover
    { assume "t < k"
      moreover have "\<And>n. t < n \<Longrightarrow> n \<le> k \<Longrightarrow> (derivative_hist_raw (worldline_raw t \<sigma> \<theta> def \<tau>) t) n s = None"
        by (auto simp add: derivative_hist_raw_def)
      ultimately have "signal_of (def s) (derivative_hist_raw (worldline_raw t \<sigma> \<theta> def \<tau>) t) s k =
                       signal_of (def s) (derivative_hist_raw (worldline_raw t \<sigma> \<theta> def \<tau>) t) s t"
        by (intro signal_of_less_ind')( auto simp add: zero_option_def) }
    moreover
    { assume "t = k"
      hence "signal_of (def s) (derivative_hist_raw (worldline_raw t \<sigma> \<theta> def \<tau>) t) s k =
             signal_of (def s) (derivative_hist_raw (worldline_raw t \<sigma> \<theta> def \<tau>) t) s t"
        by auto }
    ultimately have **: "signal_of (def s) (derivative_hist_raw (worldline_raw t \<sigma> \<theta> def \<tau>) t) s k =
                         signal_of (def s) (derivative_hist_raw (worldline_raw t \<sigma> \<theta> def \<tau>) t) s t" by auto
    have "(derivative_hist_raw (worldline_raw t \<sigma> \<theta> def \<tau>) t) t = Map.empty"
      by (auto simp add: derivative_hist_raw_def)
    hence ***: "signal_of (def s) (derivative_hist_raw (worldline_raw t \<sigma> \<theta> def \<tau>) t) s t =
                signal_of (def s) (derivative_hist_raw (worldline_raw t \<sigma> \<theta> def \<tau>) t) s (t - 1)"
      using signal_of_less_sig zero_option_def  by metis
    have "0 < t \<or> t = 0"
      by auto
    moreover
    { assume "0 < t"
      hence "t - 1 < t"
        by linarith
      hence "signal_of (def s) (derivative_hist_raw (worldline_raw t \<sigma> \<theta> def \<tau>) t) s (t - 1) = snd (worldline_raw t \<sigma> \<theta> def \<tau>) s (t - 1)"
        using signal_of_derivative_hist_raw[of "t-1" "t"]  by (smt fst_conv worldline_raw_def)
      also have "... = signal_of (def s) \<theta> s (t- 1)"
        using `t- 1 < t`unfolding worldline_raw_def by auto
      also have "... = signal_of (def s) \<theta> s t"
        using signal_of_less[where \<tau>="\<theta>", OF `\<theta> t = 0`] by auto
      also have "... = signal_of (def s) \<theta> s k"
        by (metis \<open>\<forall>n\<ge>t. \<theta> n = 0\<close> \<open>t < k \<or> t = k\<close> order.strict_implies_order signal_of_less_ind)
      finally have "signal_of (def s) (derivative_hist_raw (worldline_raw t \<sigma> \<theta> def \<tau>) t) s (t - 1) = signal_of (def s) \<theta> s k"
        by auto
      hence "signal_of (def s) (derivative_hist_raw (snd (worldline2 t \<sigma> \<theta> def \<tau>)) t) s k  = signal_of (def s) \<theta> s k"
        using * ** *** by simp }
    moreover
    { assume "t = 0"
      have  "(derivative_hist_raw (worldline_raw t \<sigma> \<theta> def \<tau>) t) t = Map.empty"
        unfolding `t = 0` by (auto simp add: derivative_hist_raw_def)
      hence "signal_of (def s) (derivative_hist_raw (worldline_raw t \<sigma> \<theta> def \<tau>) t) s t =  def s"
        using signal_of_zero unfolding `t = 0` by (metis zero_option_def)
      also have "... = signal_of (def s) \<theta> s 0"
        using `\<theta> t = 0` unfolding `t = 0` using signal_of_zero by (metis zero_fun_def)
      also have "... = signal_of (def s) \<theta> s k"
        by (metis \<open>\<forall>n\<ge>t. \<theta> n = 0\<close> \<open>t < k \<or> t = k\<close> \<open>t = 0\<close> le0 signal_of_less_ind)
      finally have "signal_of (def s) (derivative_hist_raw (worldline_raw t \<sigma> \<theta> def \<tau>) t) s t = signal_of (def s) \<theta> s k"
        by auto
      hence "signal_of (def s) (derivative_hist_raw (snd (worldline2 t \<sigma> \<theta> def \<tau>)) t) s k   = signal_of (def s) \<theta> s k"
        using * ** by auto }
    ultimately have "signal_of (def s) (derivative_hist_raw (snd (worldline2 t \<sigma> \<theta> def \<tau>)) t) s k   = signal_of (def s) \<theta> s k"
      by auto }
  ultimately show "signal_of (def s) (derivative_hist_raw (snd (worldline2 t \<sigma> \<theta> def \<tau>)) t) s k   = signal_of (def s) \<theta> s k"
    by auto
qed

lemma event_worldline2':
  assumes "context_invariant t \<sigma> \<gamma> \<theta> def \<tau>"
  shows "{s. wline_of (worldline2 t \<sigma> \<theta> def \<tau>) s t \<noteq> signal_of (def s) (derivative_hist_raw (snd (worldline2 t \<sigma> \<theta> def \<tau>)) t) s (t - 1)} = \<gamma>"
proof -
  have "\<forall>n\<le>t. \<tau> n = 0" and "\<forall>n. t \<le> n \<longrightarrow>  \<theta> n = 0"
    using assms unfolding context_invariant_def by auto
  hence *: "(\<lambda>s. wline_of (worldline2 t \<sigma> \<theta> def \<tau>) s t) = \<sigma>"
    by (intro state_worldline2)
  have **: "\<gamma> = {s. \<sigma> s \<noteq> signal_of (def s) \<theta> s (t - 1)}"
    using `context_invariant t \<sigma> \<gamma> \<theta> def \<tau>` unfolding context_invariant_def by auto
  have "{s. snd (worldline_raw t \<sigma> \<theta> def \<tau>) s t \<noteq> signal_of (def s) (derivative_hist_raw (worldline_raw t \<sigma> \<theta> def \<tau>) t) s (t - 1)} =
        {s. \<sigma> s \<noteq> signal_of (def s) (derivative_hist_raw (worldline_raw t \<sigma> \<theta> def \<tau>) t) s (t - 1)}"
    by (metis (no_types, lifting) \<open>\<forall>n\<le>t. \<tau> n = 0\<close> state_of_world state_of_world_def)
  moreover have "\<And>s. signal_of (def s) \<theta> s (t - 1) =
                      signal_of (def s) (derivative_hist_raw (worldline_raw t \<sigma> \<theta> def \<tau>) t) s (t - 1)"
    using hist_of_worldline
    by (smt One_nat_def Suc_le_lessD \<open>\<forall>n\<ge>t. \<theta> n = 0\<close> derivative_hist_raw_def diff_is_0_eq' diff_less
    fst_conv le_eq_less_or_eq signal_of_derivative_hist_raw signal_of_zero snd_conv
    worldline_raw_def zero_fun_def zero_option_def zero_order(5))
  ultimately have "{s. snd (worldline_raw t \<sigma> \<theta> def \<tau>) s t \<noteq> signal_of (def s) (derivative_hist_raw (worldline_raw t \<sigma> \<theta> def \<tau>) t) s (t - 1)} =
                   {s. \<sigma> s \<noteq> signal_of (def s) \<theta> s (t - 1)}"
    by auto
  thus ?thesis
    using **  by (simp add: worldline2_def)
qed

lemma transaction_worldline2:
  assumes "\<forall>n. n \<le> t \<longrightarrow>  \<tau> n = 0"
  assumes "\<forall>n. t \<le> n \<longrightarrow>  \<theta> n = 0"
  shows "\<And>k s . signal_of (\<sigma> s) (derivative_raw (snd (worldline2 t \<sigma> \<theta> def \<tau>)) t) s k = signal_of (\<sigma> s) \<tau> s k"
proof -
  fix k s
  have "\<tau> t s = 0"
    using assms  by (simp add: zero_fun_def)
  hence "\<And>n. n \<le> t \<Longrightarrow> \<tau> n s = 0"
    using assms by (auto)
  hence "signal_of (\<sigma> s) \<tau> s t = signal_of (\<sigma> s) \<tau> s 0"
    by (meson le0 signal_of_less_ind')
  also have "... = \<sigma> s"
    using `\<And>n. n \<le> t \<Longrightarrow> \<tau> n s = 0` by (metis le0 signal_of_zero)
  finally have "signal_of (\<sigma> s) \<tau> s t = \<sigma> s"
    by auto
  hence "snd (worldline_raw t \<sigma> \<theta> def \<tau>) s t = \<sigma> s"
    by (simp add: worldline_raw_def)
  have "k < t \<or> t \<le> k"
    by auto
  moreover
  { assume "k < t"
    have "signal_of (\<sigma> s) (derivative_raw (worldline_raw t \<sigma> \<theta> def \<tau>) t) s k = \<sigma> s"
      using signal_of2_derivative_before_now \<open>k < t\<close>  by metis
    moreover have "signal_of (\<sigma> s) \<tau> s k = \<sigma> s"
    proof -
      have "\<forall>n\<in>dom (to_trans_raw_sig \<tau> s). k < n"
      proof (rule ccontr)
        assume "\<not> (\<forall>n\<in>dom ( (to_trans_raw_sig \<tau> s)). k < n)"
        then obtain n where "n \<in> dom ( (to_trans_raw_sig \<tau> s))" and "n \<le> k"
          using leI by blast
        hence " \<tau> n = 0"
          using assms \<open>k < t\<close> by auto
        hence "n \<notin> dom ( (to_trans_raw_sig \<tau> s))"
          unfolding to_trans_raw_sig_def  by (simp add: domIff zero_fun_def zero_option_def)
        with `n \<in> dom ( (to_trans_raw_sig \<tau> s))` show False by auto
      qed
      hence "Femto_VHDL_raw.inf_time (to_trans_raw_sig \<tau>) s k = None"
        by (auto simp add: inf_time_none_iff)
      thus ?thesis
        unfolding Femto_VHDL_raw.to_signal_def comp_def by auto
    qed
    ultimately have "signal_of (\<sigma> s) (derivative_raw (worldline_raw t \<sigma> \<theta> def \<tau>) t) s k =
                     signal_of (\<sigma> s) \<tau> s k"
      by auto }
  moreover
  { assume "t \<le> k"
    hence "signal_of (\<sigma> s) (derivative_raw (worldline_raw t \<sigma> \<theta> def \<tau>)  t) s k = snd (worldline_raw t \<sigma> \<theta> def \<tau>) s k"
      using signal_of_derivative_raw `snd (worldline_raw t \<sigma> \<theta> def \<tau>) s t = \<sigma> s` by metis
    also have "... = signal_of (\<sigma> s) \<tau> s k"
      unfolding worldline_raw_def using `t \<le> k` by auto
    finally have "signal_of (\<sigma> s) (derivative_raw (worldline_raw t \<sigma> \<theta> def \<tau>)  t) s k =
                  signal_of (\<sigma> s) \<tau> s k"
      by auto }
  ultimately have "signal_of (\<sigma> s) (derivative_raw (worldline_raw t \<sigma> \<theta> def \<tau>) t) s k =
                   signal_of (\<sigma> s) \<tau> s k" by auto
  thus "signal_of (\<sigma> s) (derivative_raw (snd (worldline2 t \<sigma> \<theta> def \<tau>)) t) s k = signal_of (\<sigma> s) \<tau> s k"
    by (simp add: worldline2_def)
qed

hide_const Poly_Mapping.keys
hide_fact Poly_Mapping.keys_def

text \<open>The following definition is an attempt to define a condition such that the derivative @{term
"derivative_raw"} and @{term "derivative_hist_raw"} are the inverses of the integral (@{term
"signal_of"}). The predicate non-stuttering below indicates that, in each signal, there are no two
successive posting which has the same value. For example, if @{term "t1"} and @{term "t2"} are
elements of @{term "keys (to_trans_raw_sig \<tau> sig)"}, then the value of posted at @{term "t1"} and
@{term "t2"} are different. That is, @{term "the ((to_trans_raw_sig \<tau> sig) t1) \<noteq>
the ((to_trans_raw_sig \<tau> sig) t2)"}.

We must pay a special attention for the first key
@{term "k = hd (sorted_list_of_set (keys (\<tau> s)))"}. The first key must be
different from the default state @{term "\<sigma> s"}.\<close>

lemma derivative_raw_of_worldline2:
  assumes "\<forall>n. n \<le> t \<longrightarrow>  \<tau> n = 0"
  assumes "\<forall>s. non_stuttering (to_trans_raw_sig \<tau>) \<sigma> s"
  shows "derivative_raw (snd (worldline2 t \<sigma> \<theta> def \<tau>)) t = \<tau>"
  using assms unfolding worldline2_def
  by (simp add: derivative_raw_of_worldline_specific)

lemma derivative_is_history2:
  assumes "\<forall>n. t \<le> n \<longrightarrow>  \<theta> n = 0"
  assumes "\<forall>s. non_stuttering (to_trans_raw_sig \<theta>) def s"
  shows "derivative_hist_raw (snd (worldline2 t \<sigma> \<theta> def \<tau>)) t = \<theta>"
  using derivative_is_history unfolding worldline2_def
  by (simp add: derivative_is_history assms(1) assms(2))

text \<open>Several lemmas about preserving non_stuttering property.\<close>

lemma b_conc_exec_preserves_non_stuttering:
  assumes "t, \<sigma>, \<gamma>, \<theta>, def \<turnstile> <cs, \<tau>> \<longrightarrow>\<^sub>c \<tau>'"
  assumes "non_stuttering (to_trans_raw_sig \<tau>) \<sigma> s"
  assumes "\<And>n. n \<le> t \<Longrightarrow> \<tau> n = 0"
  assumes "nonneg_delay_conc cs"
  assumes "conc_stmt_wf cs"
  shows "non_stuttering (to_trans_raw_sig \<tau>') \<sigma> s"
  using assms
proof (induction cs arbitrary: \<tau> \<tau>')
  case (Bpar cs1 cs2)
  hence "nonneg_delay_conc cs1" and "conc_stmt_wf cs1" and "nonneg_delay_conc cs2" and "conc_stmt_wf cs2"
    by auto
  obtain \<tau>1 where \<tau>1_def: "b_conc_exec t \<sigma> \<gamma> \<theta> def cs1 \<tau> \<tau>1"
    using Bpar.prems(1) by blast
  hence "non_stuttering (to_trans_raw_sig \<tau>1) \<sigma> s"
    using Bpar(1)[OF _ Bpar(4-5)]  `nonneg_delay_conc cs1` `conc_stmt_wf cs1` by metis
  obtain \<tau>2 where \<tau>2_def: "b_conc_exec t \<sigma> \<gamma> \<theta> def cs2 \<tau> \<tau>2"
    using Bpar.prems(1) by blast
  hence "non_stuttering (to_trans_raw_sig \<tau>2) \<sigma> s"
    using Bpar(2)[OF _ Bpar(4-5)] `nonneg_delay_conc cs2` `conc_stmt_wf cs2`
    by auto
  have \<tau>'_def: "\<tau>' = clean_zip_raw \<tau> (\<tau>1, set (signals_from cs1)) (\<tau>2, set (signals_from cs2))"
    using Bpar  \<tau>1_def \<tau>2_def  by (metis obtain_clean_zip)
  have "s \<in> set (signals_from cs1) \<or> s \<in> set (signals_from cs2) \<or> s \<notin> set (signals_from cs1) \<and> s \<notin> set (signals_from cs2)"
    by auto
  moreover
  { assume "s \<in> set (signals_from cs1)"
    hence "\<And>n. \<tau>' n s = \<tau>1 n s"
      using \<tau>'_def unfolding clean_zip_raw_def Let_def by auto
    hence " (to_trans_raw_sig \<tau>' s) = (to_trans_raw_sig \<tau>1 s)"
      by (auto simp add: to_trans_raw_sig_def)
    hence ?case
      using `non_stuttering (to_trans_raw_sig \<tau>1) \<sigma> s` unfolding non_stuttering_def Let_def
      by auto }
  moreover
  { assume "s \<in> set (signals_from cs2)"
    hence "s \<notin> set (signals_from cs1)"
      using `conc_stmt_wf (cs1 || cs2)` unfolding conc_stmt_wf_def by auto
    hence "\<And>n. \<tau>' n s = \<tau>2 n s"
      using \<tau>'_def `s \<in> set (signals_from cs2)` unfolding clean_zip_raw_def Let_def
      by auto
    hence " (to_trans_raw_sig \<tau>' s) = (to_trans_raw_sig \<tau>2 s)"
      by transfer' (auto simp add: to_trans_raw_sig_def)
    hence ?case
      using `non_stuttering (to_trans_raw_sig \<tau>2) \<sigma> s` unfolding non_stuttering_def Let_def
      by auto }
  moreover
  { assume "s \<notin> set (signals_from cs1) \<and> s \<notin> set (signals_from cs2)"
    hence "\<And>n. \<tau>' n s = \<tau> n s"
      unfolding \<tau>'_def clean_zip_raw_def Let_def by auto
    hence " (to_trans_raw_sig \<tau>' s) = (to_trans_raw_sig \<tau> s)"
      by (auto simp add: to_trans_raw_sig_def)
    hence ?case
      using `non_stuttering (to_trans_raw_sig \<tau>) \<sigma> s` unfolding non_stuttering_def Let_def
      by auto }
  ultimately show ?case by auto
next
  case (Bsingle x1 x2)
  then show ?case
    using b_seq_exec_preserves_non_stuttering by force
qed

lemma init'_preserves_non_stuttering:
  assumes "init' t \<sigma> \<gamma> \<theta> def cs \<tau> \<tau>'"
  assumes "non_stuttering (to_trans_raw_sig \<tau>) \<sigma> s"
  assumes "\<And>n. n \<le> t \<Longrightarrow> \<tau> n = 0"
  assumes "nonneg_delay_conc cs"
  assumes "conc_stmt_wf cs"
  shows "non_stuttering (to_trans_raw_sig \<tau>') \<sigma> s"
  using assms
proof (induction cs arbitrary: \<tau> \<tau>')
  case (Bpar cs1 cs2)
  hence "nonneg_delay_conc cs1" and "conc_stmt_wf cs1" and "nonneg_delay_conc cs2" and "conc_stmt_wf cs2"
    by auto
  obtain \<tau>1 where \<tau>1_def : "init' t \<sigma> \<gamma> \<theta> def cs1 \<tau> \<tau>1"
    using Bpar.prems(1) by blast
  hence "non_stuttering (to_trans_raw_sig \<tau>1) \<sigma> s"
    using Bpar(1)[OF _ Bpar(4-5)]  `nonneg_delay_conc cs1` `conc_stmt_wf cs1` by metis
  obtain \<tau>2 where \<tau>2_def : "init' t \<sigma> \<gamma> \<theta> def cs2 \<tau> \<tau>2"
    using Bpar.prems(1) by blast
  hence "non_stuttering (to_trans_raw_sig \<tau>2) \<sigma> s"
    using Bpar(2)[OF _ Bpar(4-5)] `nonneg_delay_conc cs2` `conc_stmt_wf cs2`
    by auto
  have \<tau>'_def: "\<tau>' = clean_zip_raw \<tau> (\<tau>1, set (signals_from cs1)) (\<tau>2, set (signals_from cs2))"
    using Bpar  \<tau>1_def \<tau>2_def  by (meson init'.intros(2) init'_deterministic)
  have "s \<in> set (signals_from cs1) \<or> s \<in> set (signals_from cs2) \<or> s \<notin> set (signals_from cs1) \<and> s \<notin> set (signals_from cs2)"
    by auto
  moreover
  { assume "s \<in> set (signals_from cs1)"
    hence "\<And>n. \<tau>' n s = \<tau>1 n s"
      using \<tau>'_def unfolding clean_zip_raw_def Let_def by auto
    hence " (to_trans_raw_sig \<tau>' s) = (to_trans_raw_sig \<tau>1 s)"
      by (auto simp add: to_trans_raw_sig_def)
    hence ?case
      using `non_stuttering (to_trans_raw_sig \<tau>1) \<sigma> s` unfolding non_stuttering_def Let_def
      by auto }
  moreover
  { assume "s \<in> set (signals_from cs2)"
    hence "s \<notin> set (signals_from cs1)"
      using `conc_stmt_wf (cs1 || cs2)` unfolding conc_stmt_wf_def by auto
    hence "\<And>n. \<tau>' n s = \<tau>2 n s"
      using \<tau>'_def `s \<in> set (signals_from cs2)` unfolding clean_zip_raw_def Let_def
      by auto
    hence " (to_trans_raw_sig \<tau>' s) = (to_trans_raw_sig \<tau>2 s)"
      by transfer' (auto simp add: to_trans_raw_sig_def)
    hence ?case
      using `non_stuttering (to_trans_raw_sig \<tau>2) \<sigma> s` unfolding non_stuttering_def Let_def
      by auto }
  moreover
  { assume "s \<notin> set (signals_from cs1) \<and> s \<notin> set (signals_from cs2)"
    hence "\<And>n. \<tau>' n s = \<tau> n s"
      unfolding \<tau>'_def clean_zip_raw_def Let_def by auto
    hence " (to_trans_raw_sig \<tau>' s) = (to_trans_raw_sig \<tau> s)"
      by (auto simp add: to_trans_raw_sig_def)
    hence ?case
      using `non_stuttering (to_trans_raw_sig \<tau>) \<sigma> s` unfolding non_stuttering_def Let_def
      by auto }
  ultimately show ?case by auto
next
  case (Bsingle x1 x2)
  then show ?case
    using b_seq_exec_preserves_non_stuttering by force
qed

lemma [simp]:
  "fst (worldline2 t \<sigma> \<theta> def \<tau>) = t"
  unfolding worldline2_def by auto

lemma destruct_worldline_correctness:
  assumes "context_invariant t \<sigma> \<gamma> \<theta> def \<tau>"
  assumes "destruct_worldline (worldline2 t \<sigma> \<theta> def \<tau>) = (t', \<sigma>', \<gamma>', \<theta>', def' , \<tau>')"
  shows "t = t'"
    and "\<sigma> = \<sigma>'"
    and "\<gamma> = \<gamma>'"
    and "\<And>k s. signal_of (def s) \<theta> s k = signal_of (def s) \<theta>' s k"
    and "\<And>k s. signal_of (\<sigma> s) \<tau> s k = signal_of (\<sigma> s) \<tau>' s k"
    and "def' = def"
proof -
  show "t = t'"
    by (metis assms(2) fst_conv fst_destruct_worldline worldline2_def)
next
  have *: "\<forall>n\<le>t. \<tau> n = 0" and **: "\<forall>n\<ge>t. \<theta> n = 0"
    using assms unfolding context_invariant_def by auto
  thus "\<sigma> = \<sigma>'"
    using state_worldline2[OF * **] assms(2) unfolding destruct_worldline_def Let_def by auto
next
  show "\<gamma> = \<gamma>'"
    using event_worldline2'[OF assms(1)] using assms(2) unfolding destruct_worldline_def
    Let_def  by (simp add: worldline2_def worldline_raw_def)
next
  have *: "\<forall>n\<le>t. \<tau> n = 0" and **: "\<forall>n\<ge>t. \<theta> n = 0"
    using assms unfolding context_invariant_def by auto
  show "\<And>k s. signal_of (def s) \<theta> s k = signal_of (def s) \<theta>' s k"
    using hist_of_worldline[OF * **] assms(2) unfolding destruct_worldline_def Let_def by auto
next
  have *: "\<forall>n\<le>t. \<tau> n = 0" and **: "\<forall>n\<ge>t. \<theta> n = 0"
    using assms unfolding context_invariant_def by auto
  show "\<And>k s. signal_of (\<sigma> s) \<tau> s k = signal_of (\<sigma> s) \<tau>' s k"
    using transaction_worldline2[OF * **] assms(2) unfolding destruct_worldline_def Let_def by auto
next
  show " def' = def"
    by (smt assms(2) destruct_worldline_def fst_conv snd_conv worldline2_def worldline_raw_def)
qed

lemma destruct_worldline_correctness2:
  assumes "context_invariant t \<sigma> \<gamma> \<theta> def \<tau>"
  assumes "\<forall>s. non_stuttering (to_trans_raw_sig \<tau>) \<sigma> s"
  assumes " \<forall>s. non_stuttering (to_trans_raw_sig \<theta>) def s"
  assumes "destruct_worldline (worldline2 t \<sigma> \<theta> def \<tau>) = (t', \<sigma>', \<gamma>', \<theta>', def', \<tau>')"
  shows "t = t'" and "\<sigma> = \<sigma>'" and "\<gamma> = \<gamma>'" and "\<tau> = \<tau>'" and "\<theta> = \<theta>'" and "def = def'"
proof -
  show "t = t'" and "\<sigma> = \<sigma>'" and "\<gamma> = \<gamma>'"
    using destruct_worldline_correctness[OF assms(1) assms(4)] by auto
next
  have *: "\<forall>n\<le>t. \<tau> n = 0"
    using assms unfolding context_invariant_def by auto
  show "\<tau> = \<tau>'"
    using derivative_raw_of_worldline2[OF * assms(2)] assms(4) unfolding destruct_worldline_def
    Let_def by auto
next
  have **: "\<forall>n\<ge>t. \<theta> n = 0"
    using assms unfolding context_invariant_def by auto
  show "\<theta> = \<theta>'"
    using derivative_is_history2[OF ** assms(3)] assms(4) unfolding destruct_worldline_def
    Let_def by auto
next
  show "def = def'"
    using assms(1) assms(4) destruct_worldline_correctness(6) by blast
qed

lemma destruct_worldline_correctness3:
  assumes "context_invariant t \<sigma> \<gamma> \<theta> def \<tau>"
  assumes "\<forall>s. non_stuttering (to_trans_raw_sig \<tau>) \<sigma> s"
  assumes "\<forall>s. non_stuttering (to_trans_raw_sig \<theta>) def s"
  shows "destruct_worldline (worldline2 t \<sigma> \<theta> def \<tau>) = (t, \<sigma>, \<gamma>, \<theta>, def, \<tau>)"
  using destruct_worldline_correctness2[OF assms]
  by (metis (no_types, lifting) destruct_worldline_def)

lemma destruct_worldline_correctness4:
  assumes "context_invariant t \<sigma> \<gamma> \<theta> def \<tau>"
  assumes "\<forall>s. non_stuttering (to_trans_raw_sig \<tau>) \<sigma> s"
  shows   "\<exists>\<theta>'.  destruct_worldline (worldline2 t \<sigma> \<theta> def \<tau>) = (t, \<sigma>, \<gamma>, \<theta>', def, \<tau>)
              \<and> (\<forall>k s. signal_of (def s) \<theta> s k = signal_of (def s) \<theta>' s k)"
proof -
  obtain \<tau>' \<theta>' where des: "destruct_worldline (worldline2 t \<sigma> \<theta> def \<tau>) = (t, \<sigma>, \<gamma>, \<theta>', def, \<tau>')"
      and "\<And>k s. signal_of (def s) \<theta> s k = signal_of (def s) \<theta>' s k"
      and "\<And>k s. signal_of (\<sigma> s) \<tau> s k = signal_of (\<sigma> s) \<tau>' s k"
    using destruct_worldline_correctness[OF assms(1)] by (metis (no_types, lifting) destruct_worldline_def)
  have *: "\<forall>n\<le>t. \<tau> n = 0"
    using assms unfolding context_invariant_def by auto
  have "\<tau> = \<tau>'"
    using derivative_raw_of_worldline2[OF * assms(2)] des unfolding destruct_worldline_def
    Let_def by auto
  thus ?thesis
    using \<open>\<And>s k. signal_of (def s) \<theta> s k = signal_of (def s) \<theta>' s k\<close> des by blast
qed


inductive world_seq_exec :: "nat \<times> 'signal worldline_init \<Rightarrow> 'signal seq_stmt \<Rightarrow> nat \<times> 'signal worldline_init \<Rightarrow> bool"
  ("(_, _) \<Rightarrow>\<^sub>s _") where
  "   destruct_worldline tw = (t, \<sigma>, \<gamma>, \<theta>, def, \<tau>)
  \<Longrightarrow> b_seq_exec t \<sigma> \<gamma> \<theta> def s \<tau> \<tau>'
  \<Longrightarrow> worldline2 t \<sigma> \<theta> def \<tau>' = tw'
  \<Longrightarrow> world_seq_exec tw s tw'"

(* Diagram for lifting the sequential execution to the worldline level
 *
 *         w, t                    \<Rightarrow>\<^sub>s          w', t
 *           \<down>                                  \<up>
 *   destruct_worldline                      worldline2 t \<sigma> \<theta> \<tau>'
 *           \<down>                                  \<up>
 *         t, \<sigma>, \<gamma>, \<theta> \<turnstile> <s, \<tau>>    \<longrightarrow>\<^sub>s          \<tau>'
 *
 *)

inductive_cases world_seq_exec_cases : "tw, s \<Rightarrow>\<^sub>s tw'"

lemma world_seq_exec_deterministic:
  assumes "tw, s \<Rightarrow>\<^sub>s tw1"
  assumes "tw, s \<Rightarrow>\<^sub>s tw2"
  shows   "tw2 = tw1"
  using assms
  apply (induction arbitrary:tw2 rule:world_seq_exec.induct)
  using b_seq_exec_deterministic
  by (smt fst_conv snd_conv world_seq_exec_cases)

lemma time_invariant:
  assumes "tw, s \<Rightarrow>\<^sub>s tw'" shows "fst tw = fst tw'"
  using assms
  by (smt fst_conv fst_destruct_worldline world_seq_exec_cases worldline2_def)

definition
seq_hoare_valid2 :: "'signal assn2 \<Rightarrow> 'signal seq_stmt \<Rightarrow> 'signal assn2 \<Rightarrow> bool" ("\<Turnstile> [(1_)]/ (_)/ [(1_)]" 50)
where "\<Turnstile> [P] s [Q] \<longleftrightarrow>  (\<forall>tw tw'.  P tw \<and> (tw, s \<Rightarrow>\<^sub>s tw') \<longrightarrow> Q tw')"

text \<open>This is a cleaner definition of the validity compared to @{term "seq_hoare_valid"} in
@{theory "Draft.VHDL_Hoare"}. This also has the same spirit as the definition of validity in
@{theory_text "Hoare"}.\<close>

lemma beval_cong:
  assumes "beval_raw t \<sigma> \<gamma> \<theta>1 def g x"
  assumes "\<And>k s. signal_of (def s) \<theta>1 s k = signal_of (def s) \<theta>2 s k"
  shows   "beval_raw t \<sigma> \<gamma> \<theta>2 def g x"
  using assms
  by (induction rule: beval_raw.inducts) (metis beval_raw.intros)+

lemma signal_of_purge_not_affected:
  assumes "s \<noteq> sig"
  shows "signal_of (\<sigma> s) (purge_raw \<tau>1 t dly sig def val) s k = signal_of (\<sigma> s) \<tau>1 s k"
proof -
  have "\<And>n. to_trans_raw_sig (purge_raw \<tau>1 t dly sig def val) s n = to_trans_raw_sig \<tau>1 s n"
    using assms purge_raw_does_not_affect_other_sig[of "\<tau>1" "t" "dly" "sig" "def" "val" "purge_raw \<tau>1 t dly sig def val"]
    unfolding to_trans_raw_sig_def  by auto
  show ?thesis
    by (meson \<open>\<And>n. to_trans_raw_sig (purge_raw \<tau>1 t dly sig def val) s n = to_trans_raw_sig \<tau>1 s n\<close> signal_of_equal_when_trans_sig_equal_upto)
qed

lemma helper':
  assumes "t, \<sigma>, \<gamma>, \<theta>1, def \<turnstile> < ss, \<tau>1> \<longrightarrow>\<^sub>s \<tau>1'"
  assumes "\<And>k s. signal_of (def s) \<theta>1 s k = signal_of (def s) \<theta>2 s k"
  assumes "\<And>k s. signal_of (\<sigma> s) \<tau>1 s k = signal_of (\<sigma> s) \<tau>2 s k"
  assumes "t, \<sigma>, \<gamma>, \<theta>2, def \<turnstile> < ss , \<tau>2> \<longrightarrow>\<^sub>s \<tau>2'"
  assumes "\<forall>n. n \<le> t \<longrightarrow>  \<tau>1 n = 0"
  assumes "\<forall>n. n \<le> t \<longrightarrow>  \<tau>2 n = 0"
  assumes "\<forall>n. t \<le> n \<longrightarrow>  \<theta>1 n = 0"
  assumes "\<forall>n. t \<le> n \<longrightarrow>  \<theta>2 n = 0"
  assumes "nonneg_delay ss"
  assumes "\<forall>s. non_stuttering (to_trans_raw_sig \<tau>1) \<sigma> s"
  assumes "\<forall>s. non_stuttering (to_trans_raw_sig \<tau>2) \<sigma> s"
  shows "\<And>k s. signal_of (\<sigma> s) \<tau>1' s k = signal_of (\<sigma> s) \<tau>2' s k"
  using assms
proof (induction arbitrary: \<tau>2 \<tau>2' rule:b_seq_exec.inducts)
  case (1 t \<sigma> \<gamma> \<theta> def \<tau>)
  then show ?case by auto
next
  case (2 t \<sigma> \<gamma> \<theta>1 def ss1 \<tau>1 \<tau> ss2 \<tau>1')
  note IH = "2.IH"
  note prems = "2.prems"
  obtain \<tau>' where "t , \<sigma> , \<gamma> , \<theta>2, def  \<turnstile> < ss1 , \<tau>2> \<longrightarrow>\<^sub>s \<tau>'" and "t , \<sigma> , \<gamma> , \<theta>2, def  \<turnstile> < ss2 , \<tau>'> \<longrightarrow>\<^sub>s \<tau>2'"
    by (rule seq_cases_bcomp[OF \<open>t , \<sigma> , \<gamma> , \<theta>2, def  \<turnstile> <Bcomp ss1 ss2 , \<tau>2> \<longrightarrow>\<^sub>s \<tau>2'\<close>]) auto
  have "\<And>k s. signal_of (\<sigma> s) \<tau> s k = signal_of (\<sigma> s) \<tau>' s k"
    using IH(1)[OF prems(1-2) \<open>t , \<sigma> , \<gamma> , \<theta>2, def  \<turnstile> < ss1 , \<tau>2> \<longrightarrow>\<^sub>s \<tau>'\<close> prems(4-7) _ prems(9-10)]
    using nonneg_delay.simps(2) prems(8) by blast
  moreover have "\<forall>n. n \<le> t \<longrightarrow>  \<tau> n = 0"
    using "2.hyps"(1) b_seq_exec_preserve_trans_removal_nonstrict nonneg_delay.simps(2) prems(4) prems(8) by blast
  moreover have "\<forall>n. n \<le> t \<longrightarrow> \<tau>' n = 0"
    by (metis \<open>t , \<sigma> , \<gamma> , \<theta>2, def \<turnstile> < ss1 , \<tau>2> \<longrightarrow>\<^sub>s \<tau>'\<close> b_seq_exec_preserve_trans_removal_nonstrict
    nonneg_delay.simps(2) prems(5) prems(8))
  moreover  have "\<forall>a. non_stuttering (to_trans_raw_sig \<tau>) \<sigma> a"
    using b_seq_exec_preserves_non_stuttering
    by (metis "2.hyps"(1) nonneg_delay.simps(2) prems(4) prems(8) prems(9))
  moreover have "\<forall>a. non_stuttering (to_trans_raw_sig \<tau>') \<sigma> a"
    using b_seq_exec_preserves_non_stuttering
    by (metis \<open>t , \<sigma> , \<gamma> , \<theta>2, def \<turnstile> < ss1 , \<tau>2> \<longrightarrow>\<^sub>s \<tau>'\<close> nonneg_delay.simps(2) prems(10) prems(5) prems(8))
  ultimately show ?case
    using IH(2)
    by (smt \<open>t , \<sigma> , \<gamma> , \<theta>2, def \<turnstile> < ss2 , \<tau>'> \<longrightarrow>\<^sub>s \<tau>2'\<close> nonneg_delay.simps(2) prems(1) prems(6)
    prems(7) prems(8))
next
  case (3 t \<sigma> \<gamma> \<theta> def guard ss1 \<tau> \<tau>' ss2)
  have "t , \<sigma> , \<gamma> , \<theta>2, def  \<turnstile> < ss1 , \<tau>2> \<longrightarrow>\<^sub>s \<tau>2'"
    apply (rule seq_cases_bguarded[OF 3(6), rotated])
    by (metis "3.hyps"(1) "3.prems"(1) beval_cong beval_raw_deterministic val.inject(1))
  then show ?case
    using "3.IH"[OF "3.prems"(1-2) _ "3.prems"(4-7) _ "3.prems"(9-10)]
    by (metis "3.prems"(8) nonneg_delay.simps(3))
next
  case (4 t \<sigma> \<gamma> \<theta>1 def g ss2 \<tau>1 \<tau>1' ss1)
  hence "beval_raw t \<sigma> \<gamma> \<theta>2 def g (Bv False)"
    using beval_cong[OF 4(1)] by auto
  hence "b_seq_exec t \<sigma> \<gamma> \<theta>1 def ss2 \<tau>1 \<tau>1'" and "b_seq_exec t \<sigma> \<gamma> \<theta>2 def ss2 \<tau>2 \<tau>2'"
    using `beval_raw t \<sigma> \<gamma> \<theta>1 def g (Bv False)` "4.hyps"(2) apply blast
    by (metis "4.prems"(3) \<open>t , \<sigma> , \<gamma> , \<theta>2, def \<turnstile> g \<longrightarrow>\<^sub>b Bv False\<close> beval_raw_deterministic seq_cases_bguarded val.inject(1) val.sel(1))
  then show ?case
    using "4.IH"[OF "4.prems"(1-2) _ "4.prems"(4-7) _ "4.prems"(9-10)]
    by (metis "4.prems"(8) nonneg_delay.simps(3))
next
  case (5 t \<sigma> \<gamma> \<theta> def e x sig \<tau> dly \<tau>')
  have "beval_raw t \<sigma> \<gamma> \<theta>2 def e x"
    using beval_cong[OF 5(1) 5(3)] by auto
  have tau2:  "\<tau>2' = trans_post_raw sig x (\<sigma> sig) \<tau>2 t dly"
    using `beval_raw t \<sigma> \<gamma> \<theta>2 def e x` beval_raw_deterministic
    by (metis "5.prems"(3) seq_cases_trans)
  have "s \<noteq> sig \<Longrightarrow> signal_of (\<sigma> s) \<tau>' s k = signal_of (\<sigma> s) \<tau> s k"
    using signal_of_trans_post  by (metis "5.hyps"(2))
  moreover have "s \<noteq> sig \<Longrightarrow> signal_of (\<sigma> s) \<tau> s k = signal_of (\<sigma> s) \<tau>2 s k"
    using "5.prems"(2) by blast
  ultimately have *: "s \<noteq> sig \<Longrightarrow> signal_of (\<sigma> s) \<tau>' s k = signal_of (\<sigma> s) \<tau>2' s k"
    using signal_of_trans_post unfolding tau2 by metis
  have "t + dly \<le> k \<or> k < t + dly"
    by auto
  moreover
  { assume "t + dly \<le> k"
    from signal_of_trans_post3[OF this] have "signal_of (\<sigma> sig) \<tau>' sig k = x"
      by (metis "5.hyps"(2) "5.prems"(4) "5.prems"(8) less_or_eq_imp_le nonneg_delay.simps(4))
    moreover from signal_of_trans_post3[OF `t + dly \<le> k`] have "signal_of (\<sigma> sig) \<tau>2' sig k = x"
      by (metis "5.prems"(5) "5.prems"(8) nonneg_delay.simps(4) order.strict_implies_order tau2)
    ultimately have "signal_of (\<sigma> sig) \<tau>' sig k = signal_of (\<sigma> sig) \<tau>2' sig k"
      by auto
    with * have "signal_of (\<sigma> s) \<tau>' s k = signal_of (\<sigma> s) \<tau>2' s k"
      by auto }
  moreover
  { assume "k < t + dly"
    from signal_of_trans_post2[OF this] have "signal_of (\<sigma> s) \<tau>' sig k = signal_of (\<sigma> s) \<tau> sig k"
      and "signal_of (\<sigma> s) \<tau>2' sig k = signal_of (\<sigma> s) \<tau>2 sig k"
      using "5.hyps"(2) apply fastforce
      using \<open>\<And>v s' s def' def \<tau>. signal_of def (trans_post_raw s' v def' \<tau> t dly) s k = signal_of def \<tau> s k\<close> tau2
      by fastforce
    with * have "signal_of (\<sigma> s) \<tau>' s k = signal_of (\<sigma> s) \<tau>2' s k"
      using "5.prems"(2) by fastforce }
  ultimately show ?case by auto
next
  case (6 t \<sigma> \<gamma> \<theta> def e x sig \<tau>1 dly \<tau>1')
  hence "beval_raw t \<sigma> \<gamma> \<theta>2 def e x"
    using beval_cong by metis
  have tau1: "\<tau>1' = inr_post_raw sig x (\<sigma> sig) \<tau>1 t dly"
    using beval_raw_deterministic  using "6.hyps"(2) by blast
  have tau2:  "\<tau>2' = inr_post_raw sig x (\<sigma> sig) \<tau>2 t dly"
    using `beval_raw t \<sigma> \<gamma> \<theta>2 def e x`  beval_raw_deterministic
    by (metis "6.prems"(3) seq_cases_inert)
  have "s \<noteq> sig \<or> s = sig"
    by auto
  moreover
  { assume "s \<noteq> sig"
    hence ?case
      unfolding tau1 tau2
      by (metis "6.prems"(2) inr_post_raw_def signal_of_purge_not_affected signal_of_trans_post) }
  moreover
  { assume "s = sig"
    have "signal_of (\<sigma> s) \<tau>1 s t \<noteq> x \<and> signal_of (\<sigma> s) \<tau>1 s (t + dly) = x
        \<or> (signal_of (\<sigma> s) \<tau>1 s t = x \<or> signal_of (\<sigma> s) \<tau>1 s (t + dly) \<noteq> x)" (is "?earlier \<or> ?later")
      by auto
    moreover
    { assume "?earlier"
      hence earlier': "signal_of (\<sigma> s) \<tau>2 s t \<noteq> x" and "signal_of (\<sigma> s) \<tau>2  s (t + dly) = x"
        using "6.prems"(2) apply blast
        using "6.prems"(2) \<open>signal_of (\<sigma> s) \<tau>1 s t \<noteq> x \<and> signal_of (\<sigma> s) \<tau>1 s (t + dly) = x\<close> by auto
      hence "\<exists>n>t. n \<le> t + dly \<and> \<tau>2 n s = Some x"
        using switch_signal_ex_mapping[of "\<sigma>", OF earlier']
        by (simp add: "6.prems"(5) zero_fun_def)
      have "\<exists>n > t. n \<le> t + dly \<and> \<tau>1 n s = Some x"
        by (metis "6.prems"(4) \<open>signal_of (\<sigma> s) \<tau>1 s t \<noteq> x \<and> signal_of (\<sigma> s) \<tau>1 s (t + dly) = x\<close>
        switch_signal_ex_mapping zero_fun_def)
      let ?time = "GREATEST n. n \<le> t + dly \<and> \<tau>1 n s = Some x"
      let ?time2 = "GREATEST n. n \<le> t + dly \<and> \<tau>2 n s = Some x"
      have "?time \<le> ?time2"
      proof (rule Greatest_le_nat[where b="t + dly"])
        have "?time \<le> t + dly" and "\<tau>1 ?time s = Some x"
          using GreatestI_ex_nat[where P="\<lambda>n. n \<le> t + dly \<and> \<tau>1 n s = Some x" and b="t + dly"]
          `\<exists>n > t. n \<le> t + dly \<and> \<tau>1 n s = Some x` by blast+
        hence "0 < ?time"
          by (metis (no_types, lifting) "6.prems"(4) gr_zeroI le_add2 le_add_same_cancel2
          option.distinct(1) zero_fun_def zero_option_def)
        have "\<tau>2 ?time s = Some x"
        proof (rule ccontr)
          assume "\<not> \<tau>2 ?time s = Some x"
          then obtain x' where "\<tau>2 ?time s = None \<or> \<tau>2 ?time s = Some x' \<and> x' \<noteq> x"
            using option.inject by fastforce
          moreover
          { assume "\<tau>2 ?time s = Some x' \<and> x' \<noteq> x"
            hence "\<tau>2 ?time s = Some x'" and "x' \<noteq> x"
              by auto
            hence "signal_of (\<sigma> s) \<tau>2 s ?time = x'"
              using trans_some_signal_of'[of "\<tau>2" "?time" "s" "(\<lambda>s. Bv False)(s := x')" "\<sigma> s"]
              by auto
            moreover have "signal_of (\<sigma> s) \<tau>1 s ?time = x"
              using `\<tau>1 ?time s = Some x`  trans_some_signal_of'[of "\<tau>1" "?time" "s" "(\<lambda>s. Bv False)(s := x)" "\<sigma> s"]
              by auto
            ultimately have "False"
              using "6.prems"(2) \<open>x' \<noteq> x\<close> by auto }
          moreover
          { assume "\<tau>2 ?time s = None"
            hence "signal_of (\<sigma> s) \<tau>2 s ?time = signal_of (\<sigma> s) \<tau>2 s (?time - 1)"
              by (metis (no_types, lifting) signal_of_less_sig zero_option_def)
            also have "... = signal_of (\<sigma> s) \<tau>1 s (?time - 1)"
              using "6.prems"(2) by auto
            also have "... \<noteq> signal_of (\<sigma> s) \<tau>1 s ?time"
            proof (rule ccontr)
              assume "\<not> signal_of (\<sigma> s) \<tau>1 s (?time - 1) \<noteq> signal_of (\<sigma> s) \<tau>1 s ?time"
              hence th: "signal_of (\<sigma> s) \<tau>1 s ?time = signal_of (\<sigma> s) \<tau>1 s (?time - 1)"
                by auto
              have "non_stuttering (to_trans_raw_sig \<tau>1) \<sigma> s"
                by (simp add: "6.prems"(9))
              hence "\<tau>1 ?time s = 0"
                using current_sig_and_prev_same[where state="\<sigma>", OF th `0 < ?time`] by auto
              with `\<tau>1 ?time s = Some x` show False
                by (simp add: zero_option_def)
            qed
            finally have "signal_of (\<sigma> s) \<tau>2 s ?time \<noteq> signal_of (\<sigma> s) \<tau>1 s ?time"
              by auto
            hence False
              using "6.prems"(2) by auto }
          ultimately show False
            by auto
        qed
        show "?time \<le> t + dly \<and> \<tau>2 ?time s = Some x"
          using `?time \<le> t + dly`
          using \<open>\<tau>2 (GREATEST n. n \<le> t + dly \<and> \<tau>1 n s = Some x) s = Some x\<close> by blast
      next
        show " \<forall>y. y \<le> t + dly \<and> \<tau>2 y s = Some x \<longrightarrow> y \<le> t + dly"
          by auto
      qed
      have "?time2 \<le> ?time"
      proof (rule Greatest_le_nat[where b= "t + dly"])
        have "?time2 \<le> t + dly" and "\<tau>2 ?time2 s = Some x"
          using GreatestI_ex_nat[where P="\<lambda>n. n \<le> t + dly \<and> \<tau>2 n s = Some x" and b="t + dly"]
          `\<exists>n>t. n \<le> t + dly \<and> \<tau>2 n s = Some x`  by blast+
        hence "signal_of (\<sigma> s) \<tau>2 s ?time2 = x"
          using trans_some_signal_of' by fastforce
        have "\<tau>1 ?time2 s = Some x"
        proof (rule ccontr)
          assume "\<not> \<tau>1 ?time2 s = Some x"
          then obtain x' where "\<tau>1 ?time2 s = None \<or> \<tau>1 ?time2 s = Some x' \<and> x' \<noteq> x"
            using option.inject  by fastforce
          moreover
          { assume "\<tau>1 ?time2 s = Some x' \<and> x' \<noteq> x"
            hence "\<tau>1 ?time2 s  = Some x'" and "x' \<noteq> x"
              by auto
            hence "signal_of (\<sigma> s) \<tau>1 s ?time2 = x'"
              using trans_some_signal_of'[of "\<tau>1" "?time2" "s" "(\<lambda>s. Bv False)(s := x')" "\<sigma> s"]
              by simp
            with `signal_of (\<sigma> s) \<tau>2 s ?time2 = x` have False
              using \<open>x' \<noteq> x\<close> "6.prems"(2) by auto }
          moreover
          { assume "\<tau>1 ?time2 s = None"
            hence "signal_of (\<sigma> s) \<tau>1 s ?time2 = signal_of (\<sigma> s) \<tau>1 s (?time2 - 1)"
              by (metis (no_types, lifting) signal_of_less_sig zero_option_def)
            also have "... = signal_of (\<sigma> s) \<tau>2 s (?time2 - 1)"
              using "6.prems"(2) by blast
            also have "... \<noteq> signal_of (\<sigma> s) \<tau>2 s ?time2"
              using current_sig_and_prev_same
              by (metis (mono_tags) "6.prems"(10) "6.prems"(5) \<open>\<tau>2 (GREATEST n. n \<le> t + dly \<and> \<tau>2 n s
              = Some x) s = Some x\<close> not_gr_zero option.distinct(1) zero_fun_def zero_le
              zero_option_def)
            finally have "False"
              using "6.prems"(2) by blast }
          ultimately show False by auto
        qed
        thus "(GREATEST n. n \<le> t + dly \<and> \<tau>2 n s = Some x) \<le> t + dly \<and> \<tau>1 (GREATEST n. n \<le> t + dly \<and> \<tau>2 n s = Some x) s = Some x"
          using \<open>(GREATEST n. n \<le> t + dly \<and> \<tau>2 n s = Some x) \<le> t + dly\<close> by auto
      next
        show "\<forall>y. y \<le> t + dly \<and> \<tau>1 y s = Some x \<longrightarrow> y \<le> t + dly"
          by auto
      qed
      have "k < t \<or> t \<le> k \<and> k < ?time \<or> ?time \<le> k \<and> k < t + dly \<or> t + dly \<le> k"
        by auto
      moreover
      { assume "k < t"
        hence ?case
          unfolding tau1 tau2
          using signal_of_inr_post_before_now[OF `k < t`]
          by (metis "6.prems"(4) "6.prems"(5) \<open>s = sig\<close> less_imp_le_nat) }
      moreover
      { assume "t \<le> k \<and> k < ?time"
        moreover have "\<sigma> s \<noteq> x"
          using `?earlier`
          by (metis "6.prems"(4) signal_of_def zero_fun_def)
        moreover have "signal_of (\<sigma> s) \<tau>1 s (t + dly) = x" and  "signal_of (\<sigma> s) \<tau>2 s (t + dly) = x"
          using `?earlier` earlier' \<open>signal_of (\<sigma> s) \<tau>2 s (t + dly) = x\<close> by blast+
        ultimately have "signal_of (\<sigma> s) (inr_post_raw s x (\<sigma> s) \<tau>1 t dly) s k = \<sigma> s"
          unfolding tau1 apply (intro signal_of_inr_post2)
          using "6.prems"(4) by blast+
        moreover have "signal_of (\<sigma> s) (inr_post_raw s x (\<sigma> s) \<tau>2 t dly) s k = \<sigma> s"
          unfolding tau2 using `t \<le> k \<and> k < ?time` `\<sigma> s \<noteq> x` `signal_of (\<sigma> s)
          \<tau>2 s (t + dly) = x` "6.prems"(5) `t \<le> k \<and> k < ?time` `?time \<le> ?time2`
          apply (intro signal_of_inr_post2)
          using "6.prems"(5) by (linarith | blast)+
        ultimately have ?case
          unfolding tau1 tau2  by (simp add: \<open>s = sig\<close>) }
      moreover
      { assume "?time \<le> k \<and> k < t + dly"
        have "signal_of (\<sigma> s) \<tau>1 s t \<noteq> x"
          using `?earlier` by auto
        moreover have "signal_of (\<sigma> s) \<tau>1 s (t + dly) = x"
          using `?earlier` by auto
        moreover have "?time \<le> k"
          using `?time \<le> k \<and> k < t + dly` by auto
        moreover have "\<And>n. n \<le> t \<Longrightarrow> \<tau>1 n = 0"
          by (simp add: "6.prems"(4))
        ultimately have "signal_of (\<sigma> s) (inr_post_raw sig x (\<sigma> sig) \<tau>1 t dly) s k = x"
          unfolding `s = sig` by (intro signal_of_inr_post4)
        have "signal_of (\<sigma> s) \<tau>2 s t \<noteq> x"
          using earlier' by auto
        moreover have "signal_of (\<sigma> s) \<tau>2 s (t + dly) = x"
          using \<open>signal_of (\<sigma> s) \<tau>2 s (t + dly) = x\<close> by linarith
        moreover have "?time2 \<le> k"
          using `?time \<le> k \<and> k < t + dly` `?time2 \<le> ?time` by auto
        moreover have "\<And>n. n \<le> t \<Longrightarrow> \<tau>2 n = 0"
          by (simp add: "6.prems"(5))
        ultimately have "signal_of (\<sigma> s) (inr_post_raw sig x (\<sigma> sig) \<tau>2 t dly) s k = x"
          unfolding `s = sig` by (intro signal_of_inr_post4)
        hence ?case
          using \<open>signal_of (\<sigma> s) (inr_post_raw sig x (\<sigma> sig) \<tau>1 t dly) s k = x\<close> tau1 tau2
          by auto }
      moreover
      { assume "t + dly \<le> k"
        hence ?case
          by (smt "6.prems"(4-5) Suc_leI \<open>\<exists>n>t. n \<le> t + dly \<and> \<tau>2 n s
          = Some x\<close> \<open>s = sig\<close> leI le_trans less_add_same_cancel1 less_imp_le_nat not_less_eq_eq
          signal_of_inr_post tau1 tau2) }
      ultimately have ?case
        by auto }
    moreover
    { assume "?later"
      have "k < t \<or> t \<le> k \<and> k < t + dly \<or> t + dly \<le> k"
        by auto
      moreover
      { assume "k < t"
        hence ?case
          unfolding tau1 tau2 using signal_of_inr_post_before_now[OF `k < t`]
          by (metis "6.prems"(4) "6.prems"(5) \<open>s = sig\<close> less_imp_le_nat
          signal_of_inr_post_before_now) }
      moreover
      { assume "t \<le> k \<and> k < t + dly"
        hence "t \<le> k" and "k < t + dly"
          by auto
        have "signal_of (\<sigma> s) \<tau>1' s k = \<sigma> s"
          unfolding tau1 using signal_of_inr_post3[OF `t \<le> k` `k < t + dly`] `?later` `s = sig`
          by (metis (mono_tags, lifting) "6.prems"(4))
        also have "... = signal_of (\<sigma> s) \<tau>2' s k"
          unfolding tau2 using signal_of_inr_post3[OF `t \<le> k` `k < t + dly`] `?later` `s = sig`
          by (metis (mono_tags, lifting) "6.prems")
        finally have ?case
          by auto }
      moreover
      { assume "t + dly \<le> k"
        have ?case
          unfolding tau1 tau2 using signal_of_inr_post[OF `t + dly \<le> k`] `s = sig`
          by (metis "6.prems" less_imp_le_nat nonneg_delay.simps(5)) }
      ultimately have ?case
        by auto }
    ultimately have ?case
      by auto }
  ultimately show ?case
    by auto
next
  case (7 t \<sigma> \<gamma> \<theta> def exp x exp' ss \<tau> \<tau>' choices)
  have "t , \<sigma> , \<gamma> , \<theta>2, def  \<turnstile> < ss , \<tau>2> \<longrightarrow>\<^sub>s \<tau>2'"
    apply (rule seq_cases_bcase[OF 7(7), rotated])
    by (metis "7.hyps"(1) "7.hyps"(2) "7.prems"(1) Pair_inject beval_cong beval_raw_deterministic
    choices.inject list.inject) blast+
  then show ?case
    using "7.IH"[OF "7.prems"(1-2) _ "7.prems"(4-7) _ "7.prems"(9-10)] "7.prems"(8)
    by auto
next
  case (8 t \<sigma> \<gamma> \<theta> def exp x exp' x' choices \<tau> \<tau>' ss)
  have "t , \<sigma> , \<gamma> , \<theta>2, def  \<turnstile> <Bcase exp choices , \<tau>2> \<longrightarrow>\<^sub>s \<tau>2'"
    apply (rule seq_cases_bcase[OF 8(8)])
    by (metis "8.hyps"(1) "8.hyps"(2) "8.hyps"(3) "8.prems"(1) Pair_inject beval_cong
    beval_raw_deterministic choices.inject list.inject)blast+
  thus ?case
    using 8(5)[OF 8(6-7) _ 8(9-12) _ 8(14-15)] 8(13) by auto
next
  case (9 t \<sigma> \<gamma> \<theta> def ss \<tau> \<tau>' exp choices)
  hence "t , \<sigma> , \<gamma> , \<theta>2, def  \<turnstile> < ss , \<tau>2> \<longrightarrow>\<^sub>s \<tau>2'"
    using seq_cases_bcase by fastforce
  moreover have " nonneg_delay ss "
    using 9(10) by auto
  ultimately show ?case
    using 9(2)[OF 9(3-4) _ 9(6-9) _ 9(11-12)] 9(10) by auto
next
  case (10 t \<sigma> \<gamma> \<theta> def exp \<tau>)
  hence "\<tau>2' = \<tau>2"
    using seq_cases_bcase by fastforce
  then show ?case
    using 10 by auto
qed

lemma helper_goal1:
  assumes "t, \<sigma>, \<gamma>, \<theta>1, def \<turnstile> < ss, \<tau>1> \<longrightarrow>\<^sub>s \<tau>1'"
  assumes "\<And>k s. signal_of (def s) \<theta>1 s k = signal_of (def s) \<theta>2 s k"
  assumes "\<And>k s. signal_of (\<sigma> s) \<tau>1 s k = signal_of (\<sigma> s) \<tau>2 s k"
  assumes "\<forall>n. n \<le> t \<longrightarrow>  \<tau>1 n = 0"
  assumes "\<forall>n. n \<le> t \<longrightarrow>  \<tau>2 n = 0"
  assumes "\<forall>n. t \<le> n \<longrightarrow>  \<theta>1 n = 0"
  assumes "\<forall>n. t \<le> n \<longrightarrow>  \<theta>2 n = 0"
  assumes "nonneg_delay ss"
  assumes "\<forall>s. non_stuttering (to_trans_raw_sig \<tau>1) \<sigma> s"
  assumes "\<forall>s. non_stuttering (to_trans_raw_sig \<tau>2) \<sigma> s"
  shows   "\<exists>\<tau>2'. t, \<sigma>, \<gamma>, \<theta>2, def \<turnstile> < ss, \<tau>2> \<longrightarrow>\<^sub>s \<tau>2'"
  using assms
proof (induction arbitrary: \<tau>2 rule:b_seq_exec.inducts)
  case (1 t \<sigma> \<gamma> \<theta> def \<tau>)
  then show ?case by (auto intro!: b_seq_exec.intros)
next
  case (2 t \<sigma> \<gamma> \<theta> def ss1 \<tau> \<tau>'' ss2 \<tau>')
  hence "\<exists>a. t , \<sigma> , \<gamma> , \<theta>2, def  \<turnstile> < ss1 , \<tau>2> \<longrightarrow>\<^sub>s a"
    by (simp add: "2.IH"(1) "2.prems"(9))
  then obtain \<tau>2'' where "t, \<sigma>, \<gamma>, \<theta>2, def \<turnstile> < ss1, \<tau>2> \<longrightarrow>\<^sub>s \<tau>2''"
    by auto
  have *: "\<And>s k. signal_of (\<sigma> s) \<tau>'' s k = signal_of (\<sigma> s) \<tau>2'' s k"
    using helper'[OF 2(1) 2(5-6) `t, \<sigma>, \<gamma>, \<theta>2, def \<turnstile> < ss1, \<tau>2> \<longrightarrow>\<^sub>s \<tau>2''`]
    using "2.prems"(3) "2.prems"(4) "2.prems"(5) "2.prems"(6) "2.prems"(7) "2.prems"(8) "2.prems"(9) by auto
  hence "\<exists>a. t , \<sigma> , \<gamma> , \<theta>2, def  \<turnstile> < ss2 , \<tau>2''> \<longrightarrow>\<^sub>s a"
    using 2(4)[OF 2(5) *]
    by (smt "2.hyps"(1) "2.prems"(3) "2.prems"(4) "2.prems"(5) "2.prems"(6) "2.prems"(7)
    "2.prems"(8) "2.prems"(9) \<open>t , \<sigma> , \<gamma> , \<theta>2, def \<turnstile> < ss1 , \<tau>2> \<longrightarrow>\<^sub>s \<tau>2''\<close>
    b_seq_exec_preserve_trans_removal_nonstrict b_seq_exec_preserves_non_stuttering
    nonneg_delay.simps(2))
  then show ?case
    using \<open>t , \<sigma> , \<gamma> , \<theta>2, def \<turnstile> < ss1 , \<tau>2> \<longrightarrow>\<^sub>s \<tau>2''\<close> b_seq_exec.intros(2) by blast
next
  case (3 t \<sigma> \<gamma> \<theta> def guard ss1 \<tau> \<tau>' ss2)
  then show ?case
    by (metis (full_types) b_seq_exec.intros(3) beval_cong nonneg_delay.simps(3))
next
  case (4 t \<sigma> \<gamma> \<theta> def guard ss2 \<tau> \<tau>' ss1)
  then show ?case
    by (metis (full_types) b_seq_exec.intros(4) beval_cong nonneg_delay.simps(3))
next
  case (5 t \<sigma> \<gamma> \<theta> def e x sig \<tau> dly \<tau>')
  then show ?case
    by (meson b_seq_exec.intros(5) beval_cong)
next
  case (6 t \<sigma> \<gamma> \<theta> def e x sig \<tau> dly \<tau>')
  then show ?case
    by (meson b_seq_exec.intros(6) beval_cong)
next
  case (7 t \<sigma> \<gamma> \<theta> def exp x exp' ss \<tau> \<tau>' choices)
  note prems = "7.prems"
  note IH = "7.IH"
  have "nonneg_delay ss"
    using \<open>nonneg_delay (Bcase exp ((Explicit exp', ss) # choices))\<close>  unfolding nonneg_delay.simps by auto
  then obtain a where "t , \<sigma> , \<gamma> , \<theta>2, def  \<turnstile> < ss , \<tau>2> \<longrightarrow>\<^sub>s a"
    using IH[OF prems(1-6) _ prems(8-9)] by auto
  moreover have "t , \<sigma> , \<gamma> , \<theta>2, def  \<turnstile> exp \<longrightarrow>\<^sub>b x"
    using "7.hyps"(1) beval_cong prems(1) by blast
  moreover have "t , \<sigma> , \<gamma> , \<theta>2, def  \<turnstile> exp' \<longrightarrow>\<^sub>b x"
    using "7.hyps"(2) beval_cong prems(1) by blast
  ultimately have "t , \<sigma> , \<gamma> , \<theta>2, def  \<turnstile> <Bcase exp ((Explicit exp', ss) # choices) , \<tau>2> \<longrightarrow>\<^sub>s a"
    by (intro b_seq_exec.intros)
  thus ?case
    by auto
next
  case (8 t \<sigma> \<gamma> \<theta> def exp x exp' x' choices \<tau> \<tau>' ss)
  note prems = "8.prems"
  note IH = "8.IH"
  note hyps = "8.hyps"
  have "nonneg_delay (Bcase exp choices) "
    using prems(7) unfolding nonneg_delay.simps by auto
  then obtain a where "t , \<sigma> , \<gamma> , \<theta>2, def  \<turnstile> <Bcase exp choices , \<tau>2> \<longrightarrow>\<^sub>s a"
    using IH[OF prems(1-6) _ prems(8-9)] by auto
  moreover have "t , \<sigma> , \<gamma> , \<theta>2, def  \<turnstile> exp \<longrightarrow>\<^sub>b x"
    using hyps(1) beval_cong prems(1) by blast
  moreover have "t , \<sigma> , \<gamma> , \<theta>2, def  \<turnstile> exp' \<longrightarrow>\<^sub>b x'"
    using hyps(2) beval_cong prems(1) by blast
  ultimately have "t , \<sigma> , \<gamma> , \<theta>2, def  \<turnstile> <Bcase exp ((Explicit exp', ss) # choices) , \<tau>2> \<longrightarrow>\<^sub>s a"
    by (auto intro!: b_seq_exec.intros(8) simp add: \<open>x \<noteq> x'\<close>)
  thus ?case
    by blast
next
  case (9 t \<sigma> \<gamma> \<theta> def ss \<tau> \<tau>' exp choices)
  note prems = "9.prems"
  note IH = "9.IH"
  note hyps = "9.hyps"
  obtain a  where "t , \<sigma> , \<gamma> , \<theta>2, def  \<turnstile> < ss , \<tau>2> \<longrightarrow>\<^sub>s a"
    using IH[OF prems(1-6) _ prems(8-9)] prems(7) unfolding nonneg_delay.simps by auto
  hence "t , \<sigma> , \<gamma> , \<theta>2, def  \<turnstile> <Bcase exp ((Others, ss) # choices) , \<tau>2> \<longrightarrow>\<^sub>s a"
    by (intro b_seq_exec.intros)
  then show ?case
    by auto
next
  case (10 t \<sigma> \<gamma> \<theta> def exp \<tau>)
  then show ?case
    by (meson b_seq_exec.intros(10))
qed

lemma helper:
  assumes "t, \<sigma>, \<gamma>, \<theta>1, def \<turnstile> < ss, \<tau>1> \<longrightarrow>\<^sub>s \<tau>1'"
  assumes "\<And>k s. signal_of (def s) \<theta>1 s k = signal_of (def s) \<theta>2 s k"
  assumes "\<And>k s. signal_of (\<sigma> s) \<tau>1 s k = signal_of (\<sigma> s) \<tau>2 s k"
  assumes "\<forall>n. n \<le> t \<longrightarrow>  \<tau>1 n = 0"
  assumes "\<forall>n. n \<le> t \<longrightarrow>  \<tau>2 n = 0"
  assumes "\<forall>n. t \<le> n \<longrightarrow>  \<theta>1 n = 0"
  assumes "\<forall>n. t \<le> n \<longrightarrow>  \<theta>2 n = 0"
  assumes "nonneg_delay ss"
  assumes "\<forall>s. non_stuttering (to_trans_raw_sig \<tau>1) \<sigma> s"
  assumes "\<forall>s. non_stuttering (to_trans_raw_sig \<tau>2) \<sigma> s"
  shows "\<exists>\<tau>2'. (t, \<sigma>, \<gamma>, \<theta>2, def \<turnstile> < ss, \<tau>2> \<longrightarrow>\<^sub>s \<tau>2') \<and> (\<forall>k s. signal_of (\<sigma> s) \<tau>1' s k = signal_of (\<sigma> s) \<tau>2' s k)"
proof -
  have "\<exists>\<tau>2'. (t, \<sigma>, \<gamma>, \<theta>2, def \<turnstile> < ss, \<tau>2> \<longrightarrow>\<^sub>s \<tau>2')"
    using helper_goal1[OF assms] by auto
  then obtain \<tau>2' where "t, \<sigma>, \<gamma>, \<theta>2, def \<turnstile> < ss, \<tau>2> \<longrightarrow>\<^sub>s \<tau>2'"
    by blast
  thus ?thesis
    using helper'[OF assms(1-3) _ assms(4-10)] `nonneg_delay ss` by blast
qed

lemma keys_at_least_t:
  assumes "k \<in> keys (to_trans_raw_sig (derivative_raw w t) s)"
  shows "t < k"
proof (rule ccontr)
  assume "\<not> t < k" hence "k \<le> t" by auto
  hence "derivative_raw w t k s = None"
    unfolding derivative_raw_def by auto
  hence "to_trans_raw_sig (derivative_raw w t) s k = None"
    by (auto simp add: to_trans_raw_sig_def)
  hence "k \<notin> keys (to_trans_raw_sig (derivative_raw w t) s)"
    unfolding keys_def by (auto simp add: zero_option_def)
  with assms show False
    by auto
qed

lemma derivative_raw_ensure_non_stuttering:
  "\<forall>s. non_stuttering (to_trans_raw_sig (derivative_raw w t)) (\<lambda>s. snd w s t) s"
proof
  fix s
  define ks where "ks = keys (to_trans_raw_sig (derivative_raw w t) s)"
  { fix k1 k2 :: nat
    assume "k1 < k2" and "k1 \<in> ks" and "k2 \<in> ks"
    assume "\<forall>k. k1 < k \<and> k < k2 \<longrightarrow> k \<notin> ks"
    have "t < k1"
      using `k1 \<in> ks` unfolding ks_def by (simp add: keys_at_least_t)
    hence "to_trans_raw_sig (derivative_raw w t) s k1 = Some (snd w s k1)"
      using `k1 \<in> ks` unfolding ks_def keys_def to_trans_raw_sig_def derivative_raw_def
      difference_raw_def  using CollectD zero_option_def by fastforce
    moreover have "to_trans_raw_sig (derivative_raw w t) s k2 = Some (snd w s k2)"
      using `k2 \<in> ks` CollectD zero_option_def `t < k1` `k1 < k2`
      unfolding ks_def keys_def to_trans_raw_sig_def derivative_raw_def difference_raw_def
      by fastforce
    moreover have "snd w s k1 \<noteq> snd w s k2"
    proof -
      have "\<forall>k. k1 < k \<and> k < k2 \<longrightarrow> snd w s k = snd w s k1"
      proof (rule, rule)
        fix k
        assume "k1 < k \<and> k < k2"
        hence "signal_of (snd w s t) (derivative_raw w t) s k = snd w s k"
          using `t < k1`
          by(intro signal_of_derivative_raw[where \<sigma>="\<lambda>s. snd w s t"])(auto)
        hence "snd w s k = signal_of (snd w s t) (derivative_raw w t) s k"
          by auto
        also have "... = signal_of (snd w s t) (derivative_raw w t) s k1"
          using `\<forall>k. k1 < k \<and> k < k2 \<longrightarrow> k \<notin> ks` `k1 < k \<and> k < k2` unfolding ks_def
          by (intro signal_of_less_ind')(simp add: keys_def to_trans_raw_sig_def)+
        also have "... = snd w s k1"
          using `t < k1`
          by(intro signal_of_derivative_raw[where \<sigma>="\<lambda>s. snd w s t"])(auto)
        finally show "snd w s k = snd w s k1"
          by auto
      qed
      hence "snd w s (k2 - 1) = snd w s k1"
        using `k1 < k2` `t < k1`
        by (metis Suc_diff_1 diff_less less_SucE less_Suc_eq_0_disj less_imp_Suc_add zero_less_one)
      moreover have "snd w s k2 \<noteq> snd w s (k2 - 1)"
        using `k2 \<in> ks` `t < k1` `k1 < k2` zero_option_def
        unfolding ks_def keys_def to_trans_raw_sig_def derivative_raw_def difference_raw_def by force
      ultimately show ?thesis
        by auto
    qed
    ultimately have "to_trans_raw_sig (derivative_raw w t) s k1 \<noteq> to_trans_raw_sig (derivative_raw w t) s k2"
      by auto }
  note first_po = this
  { assume "ks \<noteq> {}"
    hence "\<exists>k. k \<in> ks"
      by auto
    define Least_key where "Least_key = (LEAST k. k \<in> ks)"
    have "Least_key \<in> ks"
      using LeastI_ex[OF `\<exists>k. k \<in> ks`] unfolding Least_key_def by auto
    hence "t < Least_key"
      by (simp add: keys_at_least_t ks_def)
    have "\<And>k. k < Least_key \<Longrightarrow> k \<notin> ks"
      unfolding Least_key_def using not_less_Least by blast
    hence "\<And>k. t \<le> k \<and> k < Least_key \<Longrightarrow> snd w s k = snd w s t"
    proof -
      fix k
      assume "t \<le> k \<and> k < Least_key"
      hence "signal_of (snd w s t) (derivative_raw w t) s k = snd w s k"
        by (intro signal_of_derivative_raw)(auto)
      hence "snd w s k = signal_of (snd w s t) (derivative_raw w t) s k "
        by auto
      also have "... = signal_of (snd w s t) (derivative_raw w t) s t"
        using `t \<le> k \<and> k < Least_key` `\<And>k. k < Least_key \<Longrightarrow> k \<notin> ks` `t \<le> k \<and> k < Least_key`
        by (intro signal_of_less_ind')(simp add: keys_def ks_def to_trans_raw_sig_def)+
      also have "... = signal_of (snd w s t) (derivative_raw w t) s 0"
        by (intro signal_of_less_ind')(auto simp add: derivative_raw_def zero_option_def)
      also have "... = snd w s t"
        by (metis (full_types) derivative_raw_def signal_of_zero zero_option_def zero_order(1))
      finally show "snd w s k = snd w s t"
        by auto
    qed
    moreover have "snd w s Least_key \<noteq> snd w s (Least_key - 1)"
      using `Least_key \<in> ks` `t < Least_key` unfolding ks_def keys_def to_trans_raw_sig_def
      derivative_raw_def difference_raw_def  using zero_option_def by force
    ultimately have "snd w s t \<noteq> snd w s Least_key"
      by (metis Suc_diff_1 \<open>t < Least_key\<close> diff_less less_Suc_eq_0_disj less_Suc_eq_le
      less_imp_Suc_add zero_less_one)
    moreover have "Some (snd w s Least_key) = to_trans_raw_sig (derivative_raw w t) s Least_key"
      using `Least_key \<in> ks` `t < Least_key` unfolding ks_def keys_def to_trans_raw_sig_def
      derivative_raw_def difference_raw_def using \<open>snd w s Least_key \<noteq> snd w s (Least_key - 1)\<close> by auto
    ultimately have "snd w s t \<noteq> the (to_trans_raw_sig (derivative_raw w t) s (LEAST k. k \<in> ks))"
      unfolding Least_key_def by (metis option.sel) }
  with first_po show "non_stuttering (to_trans_raw_sig (derivative_raw w t)) (\<lambda>s. snd w s t) s"
    unfolding non_stuttering_def ks_def  by blast
qed

lemma destruct_worldline_ensure_non_stuttering:
  assumes "destruct_worldline tw = (t, \<sigma>, \<gamma>, \<theta>, def, \<tau>)"
  shows "\<forall>s. non_stuttering (to_trans_raw_sig \<tau>) \<sigma> s"
proof -
  have "\<tau> = derivative_raw (snd tw) t"
    using assms  by (metis (no_types, lifting) Pair_inject destruct_worldline_def)
  moreover have  "\<sigma> = (\<lambda>s. wline_of tw s t)"
    by (metis (no_types, lifting) assms comp_apply destruct_worldline_def fst_conv snd_conv)
  ultimately show "\<forall>s. non_stuttering (to_trans_raw_sig \<tau>) \<sigma> s"
    using derivative_raw_ensure_non_stuttering[of "snd tw" "t"] by auto
qed

lemma keys_at_most_t:
  assumes "k \<in> keys (to_trans_raw_sig (derivative_hist_raw w t) s)"
  shows "k < t"
proof (rule ccontr)
  assume "\<not> k < t" hence "t \<le> k" by auto
  hence "derivative_hist_raw w t k s = None"
    unfolding derivative_hist_raw_def by auto
  hence "to_trans_raw_sig (derivative_hist_raw w t) s k = None"
    by (auto simp add: to_trans_raw_sig_def)
  hence "k \<notin> keys (to_trans_raw_sig (derivative_hist_raw w t) s)"
    unfolding keys_def by (auto simp add: zero_option_def)
  with assms show False
    by auto
qed

lemma derivative_hist_raw_ensure_non_stuttering:
  "\<forall>s. non_stuttering (to_trans_raw_sig (derivative_hist_raw w t)) (fst w) s"
proof
  fix s
  define ks where "ks = keys (to_trans_raw_sig (derivative_hist_raw w t) s)"
  { fix k1 k2 :: nat
    assume "k1 < k2" and "k1 \<in> ks" and "k2 \<in> ks"
    assume "\<forall>k. k1 < k \<and> k < k2 \<longrightarrow> k \<notin> ks"
    have "k1 < t"
      using `k1 \<in> ks` unfolding ks_def by (auto simp add: keys_at_most_t)
    hence "to_trans_raw_sig (derivative_hist_raw w t) s k1 = Some (snd w s k1)"
      using `k1 \<in> ks` unfolding ks_def keys_def to_trans_raw_sig_def derivative_hist_raw_def
      difference_raw_def  using CollectD zero_option_def
    proof -
      assume "k1 \<in> {k. (if t \<le> k then Map.empty else if k = 0 then \<lambda>s. if snd w s k \<noteq> get_time w s then Some (snd w s k) else None else (\<lambda>s. if snd w s k \<noteq> snd w s (k - 1) then Some (snd w s k) else None)) s \<noteq> 0}"
      then have f1: "(if t \<le> k1 then Map.empty else if k1 = 0 then \<lambda>a. if snd w a k1 \<noteq> get_time w a then Some (snd w a k1) else None else (\<lambda>a. if snd w a k1 \<noteq> snd w a (k1 - 1) then Some (snd w a k1) else None)) s \<noteq> 0"
        by force
      then have f2: "\<not> (if t \<le> k1 then (None::val option) = 0 else if k1 = 0 then (if snd w s k1 \<noteq> get_time w s then Some (snd w s k1) else None) = 0 else (if snd w s k1 \<noteq> snd w s (k1 - 1) then Some (snd w s k1) else None) = 0)"
        by presburger
      have f3: "\<not> t \<le> k1"
        using f1 \<open>0 = None\<close> by force
      then have f4: "k1 = 0 \<longrightarrow> snd w s 0 \<noteq> get_time w s"
        using f2 \<open>0 = None\<close> by fastforce
      have "(if t \<le> k1 then Map.empty else if k1 = 0 then \<lambda>a. if snd w a k1 \<noteq> get_time w a then Some (snd w a k1) else None else (\<lambda>a. if snd w a k1 \<noteq> snd w a (k1 - 1) then Some (snd w a k1) else None)) s = Some (snd w s k1) \<or> k1 = 0"
        using f3 f2 \<open>0 = None\<close> by fastforce
      then show "(if t \<le> k1 then Map.empty else if k1 = 0 then \<lambda>a. if snd w a k1 \<noteq> get_time w a then Some (snd w a k1) else None else (\<lambda>a. if snd w a k1 \<noteq> snd w a (k1 - 1) then Some (snd w a k1) else None)) s = Some (snd w s k1)"
        using f4 f3 by presburger
    qed
    have "k2 < t"
      using `k2 \<in> ks` unfolding ks_def by (auto simp add: keys_at_most_t)
    hence "to_trans_raw_sig (derivative_hist_raw w t) s k2 = Some (snd w s k2)"
      using `k2 \<in> ks` `k1 < k2` unfolding ks_def keys_def to_trans_raw_sig_def derivative_hist_raw_def
      difference_raw_def  using CollectD zero_option_def by fastforce
    have "snd w s k1 \<noteq> snd w s k2"
    proof -
      have "\<forall>k. k1 < k \<and> k < k2 \<longrightarrow> snd w s k = snd w s k1"
      proof (rule, rule)
        fix k
        assume "k1 < k \<and> k < k2"
        hence "signal_of (fst w s) (derivative_hist_raw w t) s k = snd w s k"
          using `k2 < t`  by(intro signal_of_derivative_hist_raw)(auto)
        hence "snd w s k = signal_of (fst w s) (derivative_hist_raw w t) s k"
          by auto
        also have "... = signal_of (fst w s) (derivative_hist_raw w t) s k1"
          using `\<forall>k. k1 < k \<and> k < k2 \<longrightarrow> k \<notin> ks` `k1 < k \<and> k < k2` unfolding ks_def
          by (intro signal_of_less_ind')(simp add: keys_def to_trans_raw_sig_def)+
        also have "... = snd w s k1"
          using `k1 < t` by(intro signal_of_derivative_hist_raw)(auto)
        finally show "snd w s k = snd w s k1"
          by auto
      qed
      hence "snd w s (k2 - 1) = snd w s k1"
        using `k1 < k2`
        by (metis Suc_diff_1 diff_less less_SucE less_Suc_eq_0_disj less_imp_Suc_add zero_less_one)
      moreover have "snd w s k2 \<noteq> snd w s (k2 - 1)"
        using `k2 \<in> ks`  `k1 < k2` `k2 < t` zero_option_def
        unfolding ks_def keys_def to_trans_raw_sig_def derivative_hist_raw_def difference_raw_def
        by force
      ultimately show ?thesis
        by auto
    qed
    hence "to_trans_raw_sig (derivative_hist_raw w t) s k1 \<noteq>
           to_trans_raw_sig (derivative_hist_raw w t) s k2"
      using \<open>to_trans_raw_sig (derivative_hist_raw w t) s k2 = Some (snd w s k2)\<close>
      and \<open>to_trans_raw_sig (derivative_hist_raw w t) s k1 = Some (snd w s k1)\<close>
      by auto }
  note first_po = this
  { assume "ks \<noteq> {}"
    hence "\<exists>k. k \<in> ks"
      by auto
    define Least_key where "Least_key = (LEAST k. k \<in> ks)"
    have "Least_key \<in> ks"
      using LeastI_ex[OF `\<exists>k. k \<in> ks`] unfolding Least_key_def by auto
    hence "Least_key < t"
      by (simp add: keys_at_most_t ks_def)
    have "\<And>k. k < Least_key \<Longrightarrow> k \<notin> ks"
      unfolding Least_key_def using not_less_Least by blast
    hence "\<And>k. k < Least_key \<Longrightarrow> snd w s k = snd w s 0"
    proof -
      fix k
      assume "k < Least_key"
      hence "signal_of (fst w s) (derivative_hist_raw w t) s k = snd w s k"
        using `Least_key < t` by (intro signal_of_derivative_hist_raw)(auto)
      hence "snd w s k = signal_of (fst w s) (derivative_hist_raw w t) s k "
        by auto
      also have "... = signal_of (fst w s) (derivative_hist_raw w t) s 0"
        using `k < Least_key` `\<And>k. k < Least_key \<Longrightarrow> k \<notin> ks`
        by (intro signal_of_less_ind')(simp add: keys_def ks_def to_trans_raw_sig_def)+
      also have "... = snd w s 0"
        by (metis \<open>Least_key < t\<close> less_trans not_gr_zero signal_of_derivative_hist_raw)
      finally show "snd w s k = snd w s 0"
        by auto
    qed
    have "Least_key = 0 \<or> 0 < Least_key"
      by auto
    moreover
    { assume "0 < Least_key"
      hence "snd w s Least_key \<noteq> snd w s (Least_key - 1)"
        using `Least_key \<in> ks` `Least_key < t` unfolding ks_def keys_def to_trans_raw_sig_def
        derivative_hist_raw_def difference_raw_def  using zero_option_def
        by force
      hence "snd w s 0 \<noteq> snd w s Least_key"
        using \<open>0 < Least_key\<close> \<open>\<And>k. k < Least_key \<Longrightarrow> snd w s k = snd w s 0\<close>
        by (metis One_nat_def diff_Suc_less)
      moreover have "Some (snd w s Least_key) = to_trans_raw_sig (derivative_hist_raw w t) s Least_key"
        using `Least_key \<in> ks` `Least_key < t` unfolding ks_def keys_def to_trans_raw_sig_def
        derivative_hist_raw_def difference_raw_def using \<open>snd w s Least_key \<noteq> snd w s (Least_key - 1)\<close>
        by (simp add: \<open>0 < Least_key\<close>)
      ultimately have "snd w s 0 \<noteq> the (to_trans_raw_sig (derivative_hist_raw w t) s (LEAST k. k \<in> ks))"
        unfolding Least_key_def  by (metis option.sel)
      moreover have "snd w s 0 = fst w s"
      proof (rule ccontr)
        assume "snd w s 0 \<noteq> fst w s"
        hence "0 \<in> ks"
          unfolding ks_def keys_def to_trans_raw_sig_def derivative_hist_raw_def difference_raw_def
          using `0 < Least_key` `Least_key < t` by (auto simp add: zero_option_def)
        thus False
          using \<open>0 < Least_key\<close> \<open>\<And>ka. ka < Least_key \<Longrightarrow> ka \<notin> ks\<close> by blast
      qed
      ultimately have "fst w s \<noteq> the (to_trans_raw_sig (derivative_hist_raw w t) s (LEAST k. k \<in> ks))"
        by auto }
    moreover
    { assume "Least_key = 0"
      hence "0 \<in> ks"
        using `Least_key \<in> ks` by auto
      hence "derivative_hist_raw w t 0 s \<noteq> 0"
        unfolding ks_def keys_def to_trans_raw_sig_def by auto
      hence "derivative_hist_raw w t 0 s \<noteq> Some (fst w s)"
        using `Least_key < t` `Least_key = 0` unfolding derivative_hist_raw_def difference_raw_def
        by simp
      hence "fst w s \<noteq> the (to_trans_raw_sig (derivative_hist_raw w t) s (LEAST k. k \<in> ks))"
        by (metis Least_key_def \<open>Least_key = 0\<close> \<open>derivative_hist_raw w t 0 s \<noteq> 0\<close> not_None_eq
        option.sel to_trans_raw_sig_def zero_option_def) }
    ultimately have "fst w s \<noteq> the (to_trans_raw_sig (derivative_hist_raw w t) s (LEAST k. k \<in> ks))"
      by auto }
  with first_po show "non_stuttering (to_trans_raw_sig (derivative_hist_raw w t)) (fst w) s"
    unfolding non_stuttering_def ks_def by auto
qed

lemma destruct_worldline_ensure_non_stuttering_hist_raw:
  assumes "destruct_worldline tw = (t, \<sigma>, \<gamma>, \<theta>, def, \<tau>)"
  shows "\<forall>s. non_stuttering (to_trans_raw_sig \<theta>) def s"
proof -
  have "\<theta> = derivative_hist_raw (snd tw) t"
    using assms  by (metis (no_types, lifting) Pair_inject destruct_worldline_def)
  moreover have  "def = (fst o snd) tw"
    using assms
    by (metis (mono_tags, lifting) comp_apply destruct_worldline_correctness(6)
    destruct_worldline_def worldline2_constructible)
  ultimately show "\<forall>s. non_stuttering (to_trans_raw_sig \<theta>) def s"
    using derivative_hist_raw_ensure_non_stuttering[of "snd tw" "t"] by auto
qed

lemma Bcomp_hoare_valid':
  assumes "\<Turnstile> [P] s1 [Q]" and "\<Turnstile> [Q] s2 [R]"
  assumes "nonneg_delay (Bcomp s1 s2)"
  shows "\<Turnstile> [P] Bcomp s1 s2 [R]"
  unfolding seq_hoare_valid2_def
proof (rule)+
  fix tw tw' :: "nat \<times> 'a worldline_init"
  have "nonneg_delay s1" and "nonneg_delay s2"
    using assms(3) by auto
  assume "P tw \<and> (tw, Bcomp s1 s2 \<Rightarrow>\<^sub>s tw')"
  hence "P tw" and "tw, Bcomp s1 s2 \<Rightarrow>\<^sub>s tw'" by auto
  then obtain t \<sigma> \<gamma> \<theta> \<tau> \<tau>' def  where des: "destruct_worldline tw = (t, \<sigma>, \<gamma>, \<theta>, def, \<tau>)" and
    "(t, \<sigma>, \<gamma>, \<theta>, def \<turnstile> <Bcomp s1 s2, \<tau>> \<longrightarrow>\<^sub>s \<tau>')" and "tw'= worldline2 t \<sigma> \<theta> def \<tau>'"
    using destruct_worldline_exist by (smt world_seq_exec_cases)
  have "\<forall>s. non_stuttering (to_trans_raw_sig \<tau>) \<sigma> s"
    using destruct_worldline_ensure_non_stuttering[OF des] by auto
  hence "\<forall>s. non_stuttering (to_trans_raw_sig \<tau>') \<sigma> s"
    using b_seq_exec_preserves_non_stuttering[OF `t, \<sigma>, \<gamma>, \<theta>, def \<turnstile> <Bcomp s1 s2, \<tau>> \<longrightarrow>\<^sub>s \<tau>'`]
    by (meson assms(3) context_invariant_def des worldline2_constructible)
  then obtain \<tau>'' where tau1: "(t, \<sigma>, \<gamma>, \<theta>, def \<turnstile> < s1, \<tau>> \<longrightarrow>\<^sub>s \<tau>'')" and tau2: "(t, \<sigma>, \<gamma>, \<theta>, def \<turnstile> < s2, \<tau>''> \<longrightarrow>\<^sub>s \<tau>')"
    using \<open>t , \<sigma> , \<gamma> , \<theta>, def \<turnstile> <Bcomp s1 s2 , \<tau>> \<longrightarrow>\<^sub>s \<tau>'\<close> seq_cases_bcomp by blast
  have "\<forall>s. non_stuttering (to_trans_raw_sig \<tau>'') \<sigma> s"
    using b_seq_exec_preserves_non_stuttering[OF tau1]
    by (meson \<open>\<forall>s. non_stuttering (to_trans_raw_sig \<tau>) \<sigma> s\<close> assms(3) context_invariant_def des
    nonneg_delay.simps(2) worldline2_constructible)
  define tw'' where "tw'' = worldline2 t \<sigma> \<theta> def \<tau>''"
  hence "tw, s1 \<Rightarrow>\<^sub>s tw''"
    using des tau1 world_seq_exec.intros by blast
  with assms(1) have "Q tw''"
    unfolding seq_hoare_valid2_def using `P tw` by fastforce
  have "context_invariant t \<sigma> \<gamma> \<theta> def \<tau>"
    using worldline2_constructible[OF des] by auto
  hence "context_invariant t \<sigma> \<gamma> \<theta> def \<tau>''"
    using b_seq_exec_preserves_context_invariant[OF _ tau1] assms(3) by auto
  obtain \<theta>''' \<tau>''' where des2: "destruct_worldline tw'' = (t, \<sigma>, \<gamma>, \<theta>''', def, \<tau>''')" and
    sig_beh: "\<And>k s. signal_of (def s) \<theta> s k = signal_of (def s) \<theta>''' s k" and
    sig_trans: "\<And>k s. signal_of (\<sigma> s) \<tau>'' s k = signal_of (\<sigma> s) \<tau>''' s k"
    unfolding tw''_def using destruct_worldline_correctness[OF `context_invariant t \<sigma> \<gamma> \<theta> def \<tau>''`]
    by (metis (no_types, lifting) destruct_worldline_def)
  have "\<forall>s. non_stuttering (to_trans_raw_sig \<tau>''') \<sigma> s"
    using destruct_worldline_ensure_non_stuttering[OF des2] by blast
  have "context_invariant t \<sigma> \<gamma> \<theta>''' def \<tau>'''"
    using worldline2_constructible[OF des2] by auto
  obtain \<tau>4 where tau3: "t, \<sigma>, \<gamma>, \<theta>''', def \<turnstile> < s2, \<tau>'''> \<longrightarrow>\<^sub>s \<tau>4" and
    sig_trans: "\<And>k s. signal_of (\<sigma> s) \<tau>4 s k = signal_of (\<sigma> s) \<tau>' s k"
    using helper[OF tau2 sig_beh sig_trans ]  \<open>nonneg_delay s2\<close> `context_invariant t \<sigma> \<gamma> \<theta> def \<tau>''`
    `context_invariant t \<sigma> \<gamma> \<theta>''' def \<tau>'''` `\<forall>s. non_stuttering (to_trans_raw_sig \<tau>'') \<sigma> s`
    `\<forall>s. non_stuttering (to_trans_raw_sig \<tau>''') \<sigma> s` unfolding context_invariant_def
    by auto
  have "worldline2 t \<sigma> \<theta> def \<tau>' = worldline2 t \<sigma> \<theta>''' def \<tau>4"
    unfolding worldline2_def worldline_raw_def  using sig_beh sig_trans
    by presburger
  hence "tw'', s2 \<Rightarrow>\<^sub>s tw'"
    using des2 tau3 `tw'= worldline2 t \<sigma> \<theta> def \<tau>'` world_seq_exec.intros by fastforce
  with `Q tw''` show "R tw'"
    using assms(2) unfolding seq_hoare_valid2_def by blast
qed

lemma Bnull_sound_hoare2:
  "\<turnstile> [P] Bnull [Q] \<Longrightarrow> \<Turnstile> [P] Bnull [Q]"
  by (smt BnullE_hoare2 seq_cases(1) seq_hoare_valid2_def world_seq_exec_cases worldline2_constructible)

lemma Bguarded_hoare_valid2:
  assumes "\<Turnstile> [\<lambda>tw. P tw \<and> (\<exists>x. beval_world_raw2 tw g x \<and>   bval_of x)] s1 [Q]" and
          "\<Turnstile> [\<lambda>tw. P tw \<and> (\<exists>x. beval_world_raw2 tw g x \<and> \<not> bval_of x)] s2 [Q]"
  shows "\<Turnstile> [P] Bguarded g s1 s2 [Q]"
  unfolding seq_hoare_valid2_def
proof (rule)+
  fix tw  tw':: "nat \<times> 'a worldline_init"
  assume "P tw \<and> (tw, Bguarded g s1 s2 \<Rightarrow>\<^sub>s tw')"
  hence "P tw" and "tw, Bguarded g s1 s2 \<Rightarrow>\<^sub>s tw'" by auto
  obtain t \<sigma> \<gamma> \<theta> def \<tau> where "destruct_worldline tw = (t, \<sigma>, \<gamma>, \<theta>, def, \<tau>)"
    by (meson destruct_worldline_def)
  hence "fst tw = t" and "tw = worldline2 t \<sigma> \<theta> def \<tau> " and "context_invariant t \<sigma> \<gamma> \<theta> def \<tau>"
    by(auto dest!: worldline2_constructible)
  obtain \<tau>' where "t , \<sigma> , \<gamma> , \<theta>, def \<turnstile> <Bguarded g s1 s2, \<tau>> \<longrightarrow>\<^sub>s \<tau>'"
    by (smt \<open>destruct_worldline tw = (t, \<sigma>, \<gamma>, \<theta>, def, \<tau>)\<close> \<open>tw, Bguarded g s1 s2 \<Rightarrow>\<^sub>s tw'\<close> fst_conv
    snd_conv world_seq_exec_cases)
  hence "tw' = worldline2 t \<sigma> \<theta> def \<tau>'"
    using `tw, Bguarded g s1 s2 \<Rightarrow>\<^sub>s tw'` `destruct_worldline tw = (t, \<sigma>, \<gamma>, \<theta>, def, \<tau>)`
    by (smt b_seq_exec_deterministic fst_conv snd_conv world_seq_exec_cases)
  have "\<forall>s. non_stuttering (to_trans_raw_sig \<theta>) def s"
    using \<open>destruct_worldline tw = (t, \<sigma>, \<gamma>, \<theta>, def, \<tau>)\<close> destruct_worldline_ensure_non_stuttering_hist_raw by blast
  obtain x where "beval_raw t \<sigma> \<gamma> \<theta> def g x" and "is_Bv x"
    using \<open>t , \<sigma> , \<gamma> , \<theta>, def \<turnstile> <Bguarded g s1 s2 , \<tau>> \<longrightarrow>\<^sub>s \<tau>'\<close>
    by (meson seq_cases_bguarded val.disc(1))
  have "bval_of x \<or> \<not> bval_of x"
    by auto
  moreover
  { assume "bval_of x"
    hence "t, \<sigma>, \<gamma>, \<theta>, def \<turnstile> < s1, \<tau>> \<longrightarrow>\<^sub>s \<tau>'"
      using `t, \<sigma>, \<gamma>, \<theta>, def \<turnstile> <Bguarded g s1 s2, \<tau>> \<longrightarrow>\<^sub>s \<tau>'`
      \<open>is_Bv x\<close> \<open>t , \<sigma> , \<gamma> , \<theta>, def \<turnstile> g \<longrightarrow>\<^sub>b x\<close> beval_raw_deterministic val.collapse(1)
      by (metis seq_cases_bguarded val.inject(1))
    hence "beval_world_raw2 tw g x"
      using `beval_raw t \<sigma> \<gamma> \<theta> def g x` `tw = worldline2 t \<sigma> \<theta> def \<tau>` `context_invariant t \<sigma> \<gamma> \<theta> def \<tau>`
      by (simp add: \<open>\<forall>s. non_stuttering (to_trans_raw_sig \<theta>) def s\<close> beval_beval_world_raw_ci
      beval_world_raw2_def worldline2_def)
    have "tw , s1 \<Rightarrow>\<^sub>s tw'"
      using `destruct_worldline tw = (t, \<sigma>, \<gamma>, \<theta>, def ,\<tau>)` `t, \<sigma>, \<gamma>, \<theta>, def \<turnstile> < s1, \<tau>> \<longrightarrow>\<^sub>s \<tau>'`
      `tw' = worldline2 t \<sigma> \<theta> def \<tau>'` world_seq_exec.intros by blast
    with assms(1) and `P tw` have "Q tw'"
      using `beval_world_raw2 tw g x` `fst tw = t` unfolding seq_hoare_valid2_def
      using \<open>bval_of x\<close> by blast }
  moreover
  { assume "\<not> bval_of x"
    hence "t, \<sigma>, \<gamma>, \<theta>, def \<turnstile> < s2, \<tau>> \<longrightarrow>\<^sub>s \<tau>'"
      using `t, \<sigma>, \<gamma>, \<theta>, def \<turnstile> <Bguarded g s1 s2, \<tau>> \<longrightarrow>\<^sub>s \<tau>'`
      using \<open>is_Bv x\<close> \<open>t , \<sigma> , \<gamma> , \<theta>, def \<turnstile> g \<longrightarrow>\<^sub>b x\<close> beval_raw_deterministic val.collapse(1)
      by (metis seq_cases_bguarded val.inject(1))
    have "tw, s2 \<Rightarrow>\<^sub>s tw'"
      using `destruct_worldline tw = (t, \<sigma>, \<gamma>, \<theta>, def, \<tau>)` `t, \<sigma>, \<gamma>, \<theta>, def \<turnstile> < s2, \<tau>> \<longrightarrow>\<^sub>s \<tau>'`
      `tw' = worldline2 t \<sigma> \<theta> def \<tau>'` world_seq_exec.intros by blast
    with assms(2) and `P tw` have "Q tw'"
      using `fst tw = t` unfolding seq_hoare_valid2_def
      by (metis \<open>\<forall>s. non_stuttering (to_trans_raw_sig \<theta>) def s\<close> \<open>\<not> bval_of x\<close> \<open>context_invariant t \<sigma>
      \<gamma> \<theta> def \<tau>\<close> \<open>t , \<sigma> , \<gamma> , \<theta>, def \<turnstile> g \<longrightarrow>\<^sub>b x\<close> \<open>tw = worldline2 t \<sigma> \<theta> def \<tau>\<close>
      beval_beval_world_raw_ci beval_world_raw2_def snd_conv worldline2_def) }
  ultimately show "Q tw'"
    by auto
qed

lemma lift_world_trans_worldline_upd2:
  assumes "tw, Bassign_trans sig exp dly \<Rightarrow>\<^sub>s tw'"
  assumes "0 < dly"
  shows "\<exists>x. beval_world_raw2 tw exp x \<and> tw' = tw[sig, dly :=\<^sub>2 x]"
proof -
  obtain t \<sigma> \<gamma> \<theta> def \<tau> where "destruct_worldline tw = (t, \<sigma>, \<gamma>, \<theta>, def, \<tau>)"
    by (meson destruct_worldline_def)
  hence "fst tw = t" and w_def: "tw = worldline2 t \<sigma> \<theta> def \<tau> " and "context_invariant t \<sigma> \<gamma> \<theta> def \<tau>"
    by(auto dest!: worldline2_constructible)
  hence "\<forall>i<fst tw. \<tau> i = 0"
    unfolding context_invariant_def by auto
  obtain x where "beval_raw t \<sigma> \<gamma> \<theta> def exp x"
    by (smt \<open>destruct_worldline tw = (t, \<sigma>, \<gamma>, \<theta>, def, \<tau>)\<close> \<open>tw, Bassign_trans sig exp dly \<Rightarrow>\<^sub>s tw'\<close>
    fst_conv seq_cases_trans snd_conv world_seq_exec_cases)
  then obtain \<tau>' where "t , \<sigma> , \<gamma> , \<theta>, def \<turnstile> <Bassign_trans sig exp dly, \<tau>> \<longrightarrow>\<^sub>s \<tau>'"
    and "\<tau>' = trans_post_raw sig x (\<sigma> sig) \<tau> t dly"
    by (simp add: b_seq_exec.intros(5))
  moreover have "beval_raw t \<sigma> \<gamma> \<theta> def exp = beval_world_raw2 tw exp"
    using `tw = worldline2 t \<sigma> \<theta> def \<tau> ` and `context_invariant t \<sigma> \<gamma> \<theta> def \<tau>`
    by (metis \<open>destruct_worldline tw = (t, \<sigma>, \<gamma>, \<theta>, def, \<tau>)\<close> \<open>get_time tw = t\<close>
    beval_beval_world_raw_ci beval_world_raw2_def destruct_worldline_ensure_non_stuttering_hist_raw
    snd_conv worldline2_def)
  ultimately have \<tau>'_def: "\<tau>' = trans_post_raw sig x (\<sigma> sig) \<tau> t dly"
    by auto
  have "tw' = (worldline2 t \<sigma> \<theta> def \<tau>')"
    using `tw, Bassign_trans sig exp dly \<Rightarrow>\<^sub>s tw'` `destruct_worldline tw = (t, \<sigma>, \<gamma>, \<theta>, def, \<tau>)`
    \<open>t , \<sigma> , \<gamma> , \<theta>, def \<turnstile> <Bassign_trans sig exp dly , \<tau>> \<longrightarrow>\<^sub>s \<tau>'\<close>
    by (smt b_seq_exec_deterministic old.prod.inject world_seq_exec_cases)
  also have "... = tw[sig, dly:=\<^sub>2 x]"
    using w_def \<tau>'_def `0 < dly` lift_trans_post_worldline_upd[where \<sigma>="\<sigma>" and t="fst tw" and \<tau>="\<tau>"]
    `\<forall>i<fst tw. \<tau> i = 0`
    by (metis \<open>beval_raw t \<sigma> \<gamma> \<theta> def exp = beval_world_raw2 tw exp\<close> \<open>get_time tw = t\<close> \<open>t , \<sigma> , \<gamma> ,
    \<theta>, def \<turnstile> exp \<longrightarrow>\<^sub>b x\<close> beval_world_raw2_def prod.sel(2) worldline2_def worldline_upd2_def)
  finally have "tw' = tw[sig, dly:=\<^sub>2 x]"
    using `fst tw = t` by auto
  thus ?thesis
    using \<open>beval_raw t \<sigma> \<gamma> \<theta> def exp = beval_world_raw2 tw exp\<close> \<open>t , \<sigma> , \<gamma> , \<theta>, def \<turnstile> exp \<longrightarrow>\<^sub>b x\<close>
    by auto
qed

lemma Bassign_trans_sound_hoare2:
  "0 < dly \<Longrightarrow> \<turnstile> [P] Bassign_trans sig exp dly [Q] \<Longrightarrow> \<Turnstile> [P] Bassign_trans sig exp dly [Q]"
  unfolding seq_hoare_valid2_def
proof rule+
  fix tw tw' :: "nat \<times> 'a worldline_init"
  assume "0 < dly"
  assume "\<turnstile> [P] Bassign_trans sig exp dly [Q]"
  hence imp: "\<forall>tw x. P tw \<and> beval_world_raw2 tw exp x \<longrightarrow> Q( tw[sig, dly :=\<^sub>2 x])"
    by (auto dest!: BassignE_hoare2)
  assume " P tw \<and> (tw, Bassign_trans sig exp dly \<Rightarrow>\<^sub>s tw')"
  hence "P tw" and "tw, Bassign_trans sig exp dly \<Rightarrow>\<^sub>s tw'" by auto
  obtain t \<sigma> \<gamma> \<theta> def \<tau> where "destruct_worldline tw = (t, \<sigma>, \<gamma>, \<theta>, def, \<tau>)" and "fst tw = t"
    by (metis (no_types, lifting) destruct_worldline_def)
  obtain \<tau>' where "t , \<sigma> , \<gamma> , \<theta>, def \<turnstile> <Bassign_trans sig exp dly, \<tau>> \<longrightarrow>\<^sub>s \<tau>'"
    by (smt \<open>destruct_worldline tw = (t, \<sigma>, \<gamma>, \<theta>, def, \<tau>)\<close> \<open>tw, Bassign_trans sig exp dly \<Rightarrow>\<^sub>s tw'\<close> fst_conv snd_conv world_seq_exec_cases)
  hence "tw' = worldline2 t \<sigma> \<theta> def \<tau>'"
    using `tw, Bassign_trans sig exp dly \<Rightarrow>\<^sub>s tw'` `destruct_worldline tw = (t, \<sigma>, \<gamma>, \<theta>, def, \<tau>)`
    \<open>t , \<sigma> , \<gamma> , \<theta>, def \<turnstile> <Bassign_trans sig exp dly , \<tau>> \<longrightarrow>\<^sub>s \<tau>'\<close>
    by (smt b_seq_exec_deterministic fst_conv snd_conv world_seq_exec_cases)
  hence "fst tw' = t"
    by transfer'  auto
  obtain x where "beval_world_raw2 tw exp x"
    using \<open>P tw\<close> imp
    by (meson \<open>0 < dly\<close> \<open>tw, Bassign_trans sig exp dly \<Rightarrow>\<^sub>s tw'\<close> lift_world_trans_worldline_upd2)
  hence "tw' = tw[sig, dly :=\<^sub>2 x]"
    unfolding `tw' = worldline2 t \<sigma> \<theta> def \<tau>'` using `fst tw = t` `0 < dly`
    by (metis \<open>tw' = worldline2 t \<sigma> \<theta> def \<tau>'\<close> \<open>tw, Bassign_trans sig exp dly \<Rightarrow>\<^sub>s tw'\<close>
    beval_world_raw2_def beval_world_raw_deterministic lift_world_trans_worldline_upd2)
  with imp and `P tw` have "Q(tw[sig, dly :=\<^sub>2 x])"
    using `fst tw = t`
    by (metis (full_types) \<open>beval_world_raw2 tw exp x\<close> beval_world_raw2_def beval_world_raw_deterministic)
  thus "Q tw'"
    using `tw' = tw[sig, dly :=\<^sub>2 x]`
    `fst tw = t` surjective_pairing[of "tw'"]  `fst tw' = t` by auto
qed

lemma lift_world_inert_worldline_upd2:
  assumes "tw, Bassign_inert sig exp dly \<Rightarrow>\<^sub>s tw'"
  assumes "0 < dly"
  shows "\<exists>x. beval_world_raw2 tw exp x \<and> tw' = tw\<lbrakk>sig, dly :=\<^sub>2 x\<rbrakk>"
proof -
  obtain t \<sigma> \<gamma> \<theta> def \<tau> where "destruct_worldline tw = (t, \<sigma>, \<gamma>, \<theta>, def, \<tau>)"
    by (meson destruct_worldline_def)
  hence "fst tw = t" and w_def: "tw = worldline2 t \<sigma> \<theta> def \<tau> " and "context_invariant t \<sigma> \<gamma> \<theta> def \<tau>"
    by(auto dest!: worldline2_constructible)
  obtain x where "beval_raw t \<sigma> \<gamma> \<theta> def exp x"
    by (smt \<open>destruct_worldline tw = (t, \<sigma>, \<gamma>, \<theta>, def, \<tau>)\<close> assms(1) fst_conv seq_cases_inert snd_conv
    world_seq_exec_cases)
  then obtain \<tau>' where "t , \<sigma> , \<gamma> , \<theta>, def \<turnstile> <Bassign_inert sig exp dly, \<tau>> \<longrightarrow>\<^sub>s \<tau>'" and "\<tau>' = inr_post_raw sig x (\<sigma> sig) \<tau> t dly"
    by (simp add: b_seq_exec.intros(6))
  have "beval_raw t \<sigma> \<gamma> \<theta> def exp = beval_world_raw2 tw exp"
    using `tw = worldline2 t \<sigma> \<theta> def \<tau> ` and `context_invariant t \<sigma> \<gamma> \<theta> def \<tau>`
    by (metis \<open>destruct_worldline tw = (t, \<sigma>, \<gamma>, \<theta>, def, \<tau>)\<close> \<open>get_time tw = t\<close>
    beval_beval_world_raw_ci beval_world_raw2_def destruct_worldline_ensure_non_stuttering_hist_raw
    snd_conv worldline2_def)
  have "non_stuttering (to_trans_raw_sig \<tau>) \<sigma> sig"
    using destruct_worldline_ensure_non_stuttering[OF `destruct_worldline tw = (t, \<sigma>, \<gamma>, \<theta>, def, \<tau>)`]
    by auto
  have "tw' = (worldline2 t \<sigma> \<theta> def \<tau>')"
    using `tw, Bassign_inert sig exp dly \<Rightarrow>\<^sub>s tw'` `destruct_worldline tw = (t, \<sigma>, \<gamma>, \<theta>, def, \<tau>)`
    \<open>t , \<sigma> , \<gamma> , \<theta>, def \<turnstile> <Bassign_inert sig exp dly , \<tau>> \<longrightarrow>\<^sub>s \<tau>'\<close>
    by (smt b_seq_exec_deterministic fst_conv snd_conv world_seq_exec_cases)
  also have "... = tw\<lbrakk>sig, dly:=\<^sub>2 x\<rbrakk>"
    using `tw = worldline2 t \<sigma> \<theta> def \<tau>` `context_invariant t \<sigma> \<gamma> \<theta> def \<tau>`
    `t , \<sigma> , \<gamma> , \<theta>, def \<turnstile> <Bassign_inert sig exp dly, \<tau>> \<longrightarrow>\<^sub>s \<tau>'` `0 < dly`
    lift_inr_post_worldline_upd[OF _ _ `t , \<sigma> , \<gamma> , \<theta>, def \<turnstile> <Bassign_inert sig exp dly, \<tau>> \<longrightarrow>\<^sub>s \<tau>'` _
    `non_stuttering (to_trans_raw_sig \<tau>) \<sigma> sig`]
    by (metis \<open>beval_raw t \<sigma> \<gamma> \<theta> def exp = beval_world_raw2 tw exp\<close> \<open>destruct_worldline tw = (t, \<sigma>,
    \<gamma>, \<theta>, def, \<tau>)\<close> \<open>get_time tw = t\<close> \<open>t , \<sigma> , \<gamma> , \<theta>, def \<turnstile> exp \<longrightarrow>\<^sub>b x\<close> beval_world_raw2_def
    destruct_worldline_ensure_non_stuttering_hist_raw snd_conv worldline2_def
    worldline_inert_upd2_def)
  finally show ?thesis
    using `fst tw = t`
    \<open>beval_raw t \<sigma> \<gamma> \<theta> def exp = beval_world_raw2 tw exp\<close> \<open>t , \<sigma> , \<gamma> , \<theta>, def \<turnstile> exp \<longrightarrow>\<^sub>b x\<close> by auto
qed

lemma Bassign_inert_sound_hoare2:
  assumes "0 < dly"
  shows "\<turnstile> [P] Bassign_inert sig exp dly [Q] \<Longrightarrow> \<Turnstile> [P] Bassign_inert sig exp dly [Q]"
  unfolding seq_hoare_valid2_def
proof rule+
  fix tw tw' :: "nat \<times> 'a worldline_init"
  assume "\<turnstile> [P] Bassign_inert sig exp dly [Q]"
  hence imp: "\<forall>tw x. P tw \<and> beval_world_raw2 tw exp x \<longrightarrow> Q(tw \<lbrakk>sig, dly :=\<^sub>2 x\<rbrakk>)"
    by (auto dest!: Bassign_inertE_hoare2)
  assume "P tw \<and> (tw, Bassign_inert sig exp dly \<Rightarrow>\<^sub>s tw')"
  hence "P tw" and "tw, (Bassign_inert sig exp dly) \<Rightarrow>\<^sub>s tw'" by auto
  obtain t \<sigma> \<gamma> \<theta> def \<tau> where "destruct_worldline tw = (t, \<sigma>, \<gamma>, \<theta>, def, \<tau>)" and "fst tw = t"
    by (metis (no_types, lifting) destruct_worldline_def)
  obtain \<tau>' where "t , \<sigma> , \<gamma> , \<theta>, def \<turnstile> <Bassign_inert sig exp dly, \<tau>> \<longrightarrow>\<^sub>s \<tau>'"
    by (smt \<open>destruct_worldline tw = (t, \<sigma>, \<gamma>, \<theta>, def, \<tau>)\<close> \<open>tw, Bassign_inert sig exp dly \<Rightarrow>\<^sub>s tw'\<close>
    fst_conv snd_conv world_seq_exec_cases)
  hence "tw' = (worldline2 t \<sigma> \<theta> def \<tau>')"
    using `tw, Bassign_inert sig exp dly \<Rightarrow>\<^sub>s tw'` `destruct_worldline tw = (t, \<sigma>, \<gamma>, \<theta>, def, \<tau>)`
    using \<open>t , \<sigma> , \<gamma> , \<theta>, def \<turnstile> <Bassign_inert sig exp dly , \<tau>> \<longrightarrow>\<^sub>s \<tau>'\<close>
    by (smt b_seq_exec_deterministic fst_conv snd_conv world_seq_exec_cases)
  hence "fst tw' = t"
    by  auto
  obtain x where "beval_world_raw2 tw exp x"
    using \<open>P tw\<close> imp
    by (meson \<open>tw, Bassign_inert sig exp dly \<Rightarrow>\<^sub>s tw'\<close> assms lift_world_inert_worldline_upd2)
  hence "tw' = tw\<lbrakk>sig, dly :=\<^sub>2 x\<rbrakk>"
    by (metis \<open>tw, Bassign_inert sig exp dly \<Rightarrow>\<^sub>s tw'\<close> assms beval_world_raw2_def
    beval_world_raw_deterministic lift_world_inert_worldline_upd2)
  with imp and `P tw` have "Q(tw\<lbrakk>sig, dly :=\<^sub>2 x\<rbrakk>)"
    using `fst tw = t`
    by (metis (full_types) \<open>beval_world_raw2 tw exp x\<close> beval_world_raw2_def
    beval_world_raw_deterministic)
  thus "Q tw'"
    using `tw' = tw \<lbrakk> sig, dly :=\<^sub>2 x\<rbrakk>` `fst tw = t` `fst tw' = t`
    surjective_pairing[of "tw'"] by auto
qed

subsubsection \<open>Soundness and completeness\<close>

lemma bcase_others_tw_elim:
  "\<And>tw tw'.  tw, Bcase exp ((Others, ss) # choices) \<Rightarrow>\<^sub>s tw' \<Longrightarrow> tw, ss \<Rightarrow>\<^sub>s tw'"
proof -
  fix tw tw'
  assume "tw, Bcase exp ((Others, ss) # choices) \<Rightarrow>\<^sub>s tw'"
  obtain t \<sigma> \<gamma> \<theta> def \<tau> \<tau>' where des: "destruct_worldline tw = (t, \<sigma>, \<gamma>, \<theta>, def, \<tau>)" and
                                exe: "b_seq_exec t \<sigma> \<gamma> \<theta> def (Bcase exp ((Others, ss) # choices)) \<tau> \<tau>'" and
                                con: "worldline2 t \<sigma> \<theta> def \<tau>' = tw'"
    apply (rule world_seq_exec_cases[OF \<open>tw, Bcase exp ((Others, ss) # choices)  \<Rightarrow>\<^sub>s tw'\<close>])
    by auto
  hence "b_seq_exec t \<sigma> \<gamma> \<theta> def ss \<tau> \<tau>'"
    using exe seq_cases_bcase by fastforce
  thus "tw, ss \<Rightarrow>\<^sub>s tw'"
    using des con by (auto intro!: world_seq_exec.intros)
qed

lemma soundness_hoare2:
  assumes "\<turnstile> [P] s [R]"
  assumes "nonneg_delay s"
  shows "\<Turnstile> [P] s [R]"
  using assms
proof (induction rule:seq_hoare2.induct)
  case (If2 g P s1 Q s2)
  hence If1: " \<Turnstile> [\<lambda>a. g a \<and> beval_world_raw2 a P (Bv True)] s1 [Q]" and
        If2: " \<Turnstile> [\<lambda>a. g a \<and> beval_world_raw2 a P (Bv False)] s2 [Q]"
    by auto
  show ?case
    unfolding seq_hoare_valid2_def
  proof (rule, rule, rule)
    fix tw tw'
    assume "g tw \<and> tw, Bguarded P s1 s2 \<Rightarrow>\<^sub>s tw'"
    hence "g tw" and "tw, Bguarded P s1 s2 \<Rightarrow>\<^sub>s tw'"
      by auto
    have "beval_world_raw2 tw P (Bv True) \<or> beval_world_raw2 tw P (Bv False)"
      by (smt \<open>tw, Bguarded P s1 s2 \<Rightarrow>\<^sub>s tw'\<close> beval_beval_world_raw_ci beval_world_raw2_def
      destruct_worldline_ensure_non_stuttering_hist_raw fst_conv seq_cases_bguarded snd_conv
      world_seq_exec_cases worldline2_constructible worldline2_def)
    moreover
    { assume "beval_world_raw2 tw P (Bv True)"
      hence "tw, s1 \<Rightarrow>\<^sub>s tw'"
        using \<open>tw, Bguarded P s1 s2 \<Rightarrow>\<^sub>s tw'\<close>
        by (smt beval_beval_world_raw_ci beval_world_raw2_def beval_world_raw_deterministic
        destruct_worldline_ensure_non_stuttering_hist_raw fst_conv seq_cases_bguarded snd_conv
        val.inject(1) world_seq_exec.intros world_seq_exec_cases worldline2_constructible
        worldline2_def)
      hence "Q tw'"
        using If1 \<open>g tw\<close> unfolding seq_hoare_valid2_def
        using \<open>beval_world_raw2 tw P (Bv True)\<close> by blast }
    moreover
    { assume "beval_world_raw2 tw P (Bv False)"
      hence "tw, s2 \<Rightarrow>\<^sub>s tw'"
        by (smt \<open>tw, Bguarded P s1 s2 \<Rightarrow>\<^sub>s tw'\<close> beval_beval_world_raw_ci beval_world_raw2_def
        beval_world_raw_deterministic destruct_worldline_ensure_non_stuttering_hist_raw fst_conv
        seq_cases_bguarded snd_conv val.inject(1) world_seq_exec.intros world_seq_exec_cases
        worldline2_constructible worldline2_def)
      hence "Q tw'"
        using If2 \<open>g tw\<close> \<open>beval_world_raw2 tw P (Bv False)\<close> unfolding seq_hoare_valid2_def by blast }
    ultimately show "Q tw'"
      by blast
  qed
next
  case (AssignI2 exp P sig dly)
  hence "0 < dly" by auto
  then show ?case
    using Bassign_inert_sound_hoare2[OF `0 < dly`]  using seq_hoare2.AssignI2 by fastforce
next
  case (Conseq2 P' P s Q Q')
  then show ?case
    by (smt seq_hoare_valid2_def)
next
  case (Conj P s Q1 Q2)
  then show ?case by (simp add: seq_hoare_valid2_def)
next
  case (Bcase_empty_choices2 P exp)
  then show ?case unfolding seq_hoare_valid2_def
    by (smt b_seq_exec.intros(10) b_seq_exec_deterministic world_seq_exec.simps worldline2_constructible)
next
  case (Bcase_others2 P ss Q exp choices)
  hence " \<Turnstile> [P] ss [Q]"
    unfolding nonneg_delay.simps by auto
  hence "\<forall>tw tw'. P tw \<and> tw, ss \<Rightarrow>\<^sub>s tw' \<longrightarrow> Q tw'"
    unfolding seq_hoare_valid2_def by auto
  thus ?case
    using bcase_others_tw_elim unfolding seq_hoare_valid2_def by blast
next
  case (Bcase_if2 P exp exp' ss Q choices)
  hence eq: " \<Turnstile> [\<lambda>a. P a \<and> (\<exists>x. beval_world_raw2 a exp x \<and> beval_world_raw2 a exp' x)] ss [Q]"
    and neq: " \<Turnstile> [\<lambda>a. P a \<and> (\<exists>x x'. beval_world_raw2 a exp x \<and> beval_world_raw2 a exp' x' \<and> x \<noteq> x')] Bcase exp choices [Q]"
    unfolding nonneg_delay.simps by auto
  show ?case
    unfolding seq_hoare_valid2_def
  proof (rule)+
    fix tw tw'
    assume "P tw \<and> tw, Bcase exp ((Explicit exp', ss) # choices) \<Rightarrow>\<^sub>s tw'"
    hence "P tw" and "tw, Bcase exp ((Explicit exp', ss) # choices) \<Rightarrow>\<^sub>s tw'"
      by auto
    obtain t \<sigma> \<gamma> \<theta> def \<tau> \<tau>' where des: "destruct_worldline tw = (t, \<sigma>, \<gamma>, \<theta>, def, \<tau>)" and
                                  exe: "b_seq_exec t \<sigma> \<gamma> \<theta> def (Bcase exp ((Explicit exp', ss) # choices)) \<tau> \<tau>'" and
                                  con: "worldline2 t \<sigma> \<theta> def \<tau>' = tw'"
      by (rule world_seq_exec_cases[OF \<open>tw, Bcase exp ((Explicit exp', ss) # choices) \<Rightarrow>\<^sub>s tw'\<close>])
    obtain x x' where bevalx: "t , \<sigma> , \<gamma> , \<theta>, def  \<turnstile> exp \<longrightarrow>\<^sub>b x" and bevalx': "t , \<sigma> , \<gamma> , \<theta>, def  \<turnstile> exp' \<longrightarrow>\<^sub>b x'"
      by (rule seq_cases_bcase[OF exe]) blast+
      have beval2x: "beval_world_raw2 tw exp x" and beval2x': "beval_world_raw2 tw exp' x'"
        using bevalx bevalx' unfolding beval_world_raw2_def
        by (metis beval_beval_world_raw_ci des destruct_worldline_ensure_non_stuttering_hist_raw
        fst_conv snd_conv worldline2_constructible worldline2_def)+
    have "x = x' \<or> x \<noteq> x'"
      by auto
    moreover
    { assume "x = x'"
      have "b_seq_exec t \<sigma> \<gamma> \<theta> def ss \<tau> \<tau>'"
        apply (rule seq_cases_bcase[OF exe, rotated])
        using bevalx bevalx' \<open>x = x'\<close>
        by (metis beval_raw_deterministic choices.sel fst_conv list.inject) blast+
      hence "tw, ss \<Rightarrow>\<^sub>s tw'"
        by (smt con des world_seq_exec.intros)
      with eq `P tw` have "Q tw'"
        using beval2x beval2x'  unfolding \<open>x = x'\<close> seq_hoare_valid2_def by blast }
    moreover
    { assume "x \<noteq> x'"
      have "b_seq_exec t \<sigma> \<gamma> \<theta> def (Bcase exp choices) \<tau> \<tau>'"
        apply (rule seq_cases_bcase[OF exe])
        using bevalx bevalx' \<open>x \<noteq> x'\<close>
        by (metis (mono_tags, hide_lams) beval_raw_deterministic choices.sel fst_conv
            list.inject)blast+
      hence "tw, Bcase exp choices \<Rightarrow>\<^sub>s tw'"
        using con des world_seq_exec.intros by blast
      with neq `P tw` have "Q tw'"
        using beval2x beval2x' \<open>x \<noteq> x'\<close> unfolding seq_hoare_valid2_def by blast }
    ultimately show "Q tw'"
      by auto
  qed
qed (auto simp add: Bnull_sound_hoare2 Bassign_trans_sound_hoare2 Bcomp_hoare_valid' Bguarded_hoare_valid2)

lemma  world_seq_exec_bnull:
  "tw, Bnull \<Rightarrow>\<^sub>s tw"
proof -
  obtain t \<sigma> \<gamma> \<theta> def \<tau> where des: "destruct_worldline tw = (t, \<sigma>, \<gamma>, \<theta>, def, \<tau>)"
    using prod_cases6 by blast
  have seq: " t , \<sigma> , \<gamma> , \<theta>, def  \<turnstile> <Bnull , \<tau>> \<longrightarrow>\<^sub>s \<tau>"
    by (intro b_seq_exec.intros)
  have cons: "worldline2 t \<sigma> \<theta> def \<tau> = tw"
    using worldline2_constructible[OF des] by auto
  show ?thesis
    by (intro world_seq_exec.intros)(rule des, rule seq, rule cons)
qed

lemma world_seq_exec_comp':
  assumes "nonneg_delay (Bcomp ss1 ss2)"
  assumes "tw, ss1 \<Rightarrow>\<^sub>s tw''"
  assumes "tw'', ss2 \<Rightarrow>\<^sub>s tw'"
  assumes "tw, (Bcomp ss1 ss2) \<Rightarrow>\<^sub>s tw_res"
  shows "tw_res = tw'"
proof -
  obtain t \<sigma> \<gamma> \<theta> \<tau> \<tau>' def where des1: "destruct_worldline tw = (t, \<sigma>, \<gamma>, \<theta>, def, \<tau>)" and
    "t, \<sigma>, \<gamma>, \<theta>, def \<turnstile> <Bcomp ss1 ss2, \<tau>> \<longrightarrow>\<^sub>s \<tau>'" and ci1: "context_invariant t \<sigma> \<gamma> \<theta> def \<tau>"
    using destruct_worldline_exist worldline2_constructible
    by (smt assms(4) world_seq_exec_cases)
  have "\<forall>s. non_stuttering (to_trans_raw_sig \<tau>) \<sigma> s"
    using destruct_worldline_ensure_non_stuttering[OF des1] by auto
  then obtain \<tau>'' where "t, \<sigma>, \<gamma>, \<theta>, def \<turnstile> < ss1, \<tau>> \<longrightarrow>\<^sub>s \<tau>''" and exec1: "t, \<sigma>, \<gamma>, \<theta>, def \<turnstile> < ss2, \<tau>''> \<longrightarrow>\<^sub>s \<tau>'"
    and ci2: "context_invariant t \<sigma> \<gamma> \<theta> def \<tau>''" using b_seq_exec_preserves_context_invariant
    using assms \<open>t , \<sigma> , \<gamma> , \<theta>, def \<turnstile> <Bcomp ss1 ss2 , \<tau>> \<longrightarrow>\<^sub>s \<tau>'\<close> ci1
    by (metis nonneg_delay.simps(2) seq_cases_bcomp)
  hence "\<forall>s. non_stuttering (to_trans_raw_sig \<tau>'') \<sigma> s"
    using b_seq_exec_preserves_non_stuttering
    by (metis \<open>\<forall>s. non_stuttering (to_trans_raw_sig \<tau>) \<sigma> s\<close> assms ci1 context_invariant_def
    nonneg_delay.simps(2))
  hence *: "world_seq_exec tw ss1 (worldline2 t \<sigma> \<theta> def \<tau>'')"
    using des1 \<open>t , \<sigma> , \<gamma> , \<theta>, def \<turnstile> < ss1 , \<tau>> \<longrightarrow>\<^sub>s \<tau>''\<close> world_seq_exec.intros by blast
  obtain \<theta>2 \<tau>2 \<tau>3 where des2: "destruct_worldline (worldline2 t \<sigma> \<theta> def \<tau>'') = (t, \<sigma>, \<gamma>, \<theta>2, def, \<tau>2)" and
    beh_same:"\<And>s k. signal_of (def s) \<theta> s k = signal_of (def s) \<theta>2 s k" and
    trans_same: "\<And>s k. signal_of (\<sigma> s) \<tau>'' s k = signal_of (\<sigma> s) \<tau>2 s k" and
    exec2: "t, \<sigma>, \<gamma>, \<theta>2, def \<turnstile> < ss2, \<tau>2> \<longrightarrow>\<^sub>s \<tau>3"
    using destruct_worldline_correctness[OF ci2]
    by (smt "*" assms(2) assms(3) b_seq_exec_deterministic fst_conv snd_conv world_seq_exec_cases)
  have "\<forall>s. non_stuttering (to_trans_raw_sig \<tau>2) \<sigma> s"
    using destruct_worldline_ensure_non_stuttering[OF des2] by blast
  have ci3: "context_invariant t \<sigma> \<gamma> \<theta>2 def \<tau>2"
    using worldline2_constructible[OF des2] by auto
  have "\<And>s k. signal_of (\<sigma> s) \<tau>' s k = signal_of (\<sigma> s) \<tau>3 s k"
    using helper'[OF exec1 beh_same trans_same exec2] ci2 ci3
    `\<forall>s. non_stuttering (to_trans_raw_sig \<tau>'') \<sigma> s` `\<forall>s. non_stuttering (to_trans_raw_sig \<tau>2) \<sigma> s`
    unfolding context_invariant_def using assms by auto
  hence "worldline2 t \<sigma> \<theta> def \<tau>' = worldline2 t \<sigma> \<theta>2 def \<tau>3"
    using beh_same unfolding worldline2_def worldline_raw_def
    by presburger
  hence "world_seq_exec (worldline2 t \<sigma> \<theta> def \<tau>'') ss2 (worldline2 t \<sigma> \<theta>2 def \<tau>3)"
    using des2 `t, \<sigma>, \<gamma>, \<theta>2, def \<turnstile> < ss2, \<tau>2> \<longrightarrow>\<^sub>s \<tau>3`
    using world_seq_exec.intros by blast
  hence "world_seq_exec (worldline2 t \<sigma> \<theta> def \<tau>'') ss2 (worldline2 t \<sigma> \<theta> def \<tau>')"
    by (simp add: \<open>worldline2 t \<sigma> \<theta> def \<tau>' = worldline2 t \<sigma> \<theta>2 def \<tau>3\<close>)
  thus ?thesis
    using des1 `t, \<sigma>, \<gamma>, \<theta>, def \<turnstile> <Bcomp ss1 ss2, \<tau>> \<longrightarrow>\<^sub>s \<tau>'` unfolding  *
    by (smt "*" assms(2-4) b_seq_exec_deterministic fst_conv snd_conv world_seq_exec_cases)
qed

lemma world_seq_exec_comp_exist:
  assumes "nonneg_delay (Bcomp ss1 ss2)"
  assumes "tw  , ss1 \<Rightarrow>\<^sub>s tw''"
  assumes "tw'', ss2 \<Rightarrow>\<^sub>s tw'"
  shows   "\<exists>tw_res. tw, (Bcomp ss1 ss2) \<Rightarrow>\<^sub>s tw_res"
proof -
  obtain t \<sigma> \<gamma> \<theta> \<tau> \<tau>'' def where des1: "destruct_worldline tw = (t, \<sigma>, \<gamma>, \<theta>, def, \<tau>)" and
    "t, \<sigma>, \<gamma>, \<theta>, def \<turnstile> < ss1, \<tau>> \<longrightarrow>\<^sub>s \<tau>''" and ci1: "context_invariant t \<sigma> \<gamma> \<theta> def \<tau>" and
    "tw'' = worldline2 t \<sigma> \<theta> def \<tau>''"
    by (smt assms(2) world_seq_exec_cases worldline2_constructible)
  moreover have "context_invariant t \<sigma> \<gamma> \<theta> def \<tau>''"
    using assms(1) b_seq_exec_preserves_context_invariant calculation(2) ci1 nonneg_delay.simps(2)
    by blast
  moreover have "\<forall>s. non_stuttering (to_trans_raw_sig \<tau>) \<sigma> s"
    using des1 destruct_worldline_ensure_non_stuttering by blast
  moreover hence "\<forall>s. non_stuttering (to_trans_raw_sig \<tau>'') \<sigma> s"
    using b_seq_exec_preserves_non_stuttering[OF `t, \<sigma>, \<gamma>, \<theta>, def \<turnstile> < ss1, \<tau>> \<longrightarrow>\<^sub>s \<tau>''`]
    using assms(1) des1 destruct_worldline_trans_zero_upto_now nonneg_delay.simps(2) by blast
  moreover have "\<forall>s. non_stuttering (to_trans_raw_sig \<theta>) def s"
    using des1 destruct_worldline_ensure_non_stuttering_hist_raw by blast
  ultimately have "destruct_worldline tw'' = (t, \<sigma>, \<gamma>, \<theta>, def, \<tau>'')"
    by (simp add: destruct_worldline_correctness3)
  then obtain \<tau>' where "t, \<sigma>, \<gamma>, \<theta>, def \<turnstile> < ss2, \<tau>''> \<longrightarrow>\<^sub>s \<tau>'" and cons: "worldline2 t \<sigma> \<theta> def \<tau>' = tw'"
    using assms(3)
    by (smt fst_conv snd_conv world_seq_exec_cases)
  hence *: "t, \<sigma>, \<gamma>, \<theta>, def \<turnstile> <Bcomp ss1 ss2, \<tau>> \<longrightarrow>\<^sub>s \<tau>'"
    using \<open>t , \<sigma> , \<gamma> , \<theta>, def \<turnstile> < ss1 , \<tau>> \<longrightarrow>\<^sub>s \<tau>''\<close> b_seq_exec.intros(2) by blast
  thus ?thesis
    apply (intro exI[where x="tw'"])
    apply (intro world_seq_exec.intros)
      apply (rule des1)
     apply (rule *)
    apply (rule cons)
    done
qed

lemma world_seq_exec_comp:
  assumes "nonneg_delay (Bcomp ss1 ss2)"
  assumes "tw, ss1 \<Rightarrow>\<^sub>s tw''"
  assumes "tw'', ss2 \<Rightarrow>\<^sub>s tw'"
  shows "tw, (Bcomp ss1 ss2) \<Rightarrow>\<^sub>s tw'"
  using world_seq_exec_comp' world_seq_exec_comp_exist
  using assms(1) assms(2) assms(3) by blast

lemma world_seq_exec_guarded:
  fixes tw :: "nat \<times> 'a worldline_init"
  assumes "beval_world_raw2 tw g (Bv True)"
  assumes "tw, ss1 \<Rightarrow>\<^sub>s tw'"
  shows "world_seq_exec tw (Bguarded g ss1 ss2) tw'"
proof -
  obtain t \<sigma> \<gamma> \<theta> \<tau> \<tau>' def where des1: "destruct_worldline tw = (t, \<sigma>, \<gamma>, \<theta>, def, \<tau>)" and
    ex1: "t, \<sigma>, \<gamma>, \<theta>, def \<turnstile> < ss1, \<tau>> \<longrightarrow>\<^sub>s \<tau>'" and ci1: "context_invariant t \<sigma> \<gamma> \<theta> def \<tau>" and
    "tw = worldline2 t \<sigma> \<theta> def \<tau>" and "fst tw = t"
    using destruct_worldline_exist worldline2_constructible
    by (smt assms(2) fst_conv fst_destruct_worldline world_seq_exec_cases)
  have beval: "t , \<sigma> , \<gamma> , \<theta>, def  \<turnstile> g \<longrightarrow>\<^sub>b Bv True"
    by (metis \<open>get_time tw = t\<close> \<open>tw = worldline2 t \<sigma> \<theta> def \<tau>\<close> assms(1) beval_beval_world_raw_ci
    beval_world_raw2_def ci1 des1 destruct_worldline_ensure_non_stuttering_hist_raw sndI
    worldline2_def)
  have "worldline2 t \<sigma> \<theta> def \<tau>' = tw'"
    by (smt Pair_inject assms(2) b_seq_exec_deterministic des1 ex1 world_seq_exec_cases)
  thus ?thesis
    apply (intro world_seq_exec.intros)
      apply (rule des1)
     apply (intro b_seq_exec.intros)
      apply (intro beval)
     apply (rule ex1)
    apply assumption
    done
qed

lemma world_seq_exec_explicit_match:
  assumes "beval_world_raw2 tw exp x" and "beval_world_raw2 tw exp' x"
  assumes "tw, ss \<Rightarrow>\<^sub>s tw'"
  shows   "world_seq_exec tw  (Bcase exp ((Explicit exp', ss) # choices)) tw'"
  using assms
  by (smt b_seq_exec.intros(7) beval_beval_world_raw_ci beval_world_raw2_def
  destruct_worldline_ensure_non_stuttering_hist_raw prod.sel(1) prod.sel(2) world_seq_exec.intros
  world_seq_exec_cases worldline2_constructible worldline2_def)

lemma world_seq_exec_explicit_no_match:
  assumes "beval_world_raw2 tw exp x" and "beval_world_raw2 tw exp' x'" and "x \<noteq> x'"
  assumes "tw, (Bcase exp choices) \<Rightarrow>\<^sub>s tw'"
  shows   "world_seq_exec tw  (Bcase exp ((Explicit exp', ss) # choices)) tw'"
  using assms
  by (smt b_seq_exec.intros(8) beval_beval_world_raw_ci beval_world_raw2_def
  destruct_worldline_ensure_non_stuttering_hist_raw fst_conv snd_conv world_seq_exec.intros
  world_seq_exec_cases worldline2_constructible worldline2_def)

lemma world_seq_exec_guarded_not:
  fixes tw :: "nat \<times> 'a worldline_init"
  assumes "beval_world_raw2 tw g (Bv False)"
  assumes "tw, ss2 \<Rightarrow>\<^sub>s tw'"
  shows "world_seq_exec tw (Bguarded g ss1 ss2) tw'"
proof -
  obtain t \<sigma> \<gamma> \<theta> \<tau> \<tau>' def where des1: "destruct_worldline tw = (t, \<sigma>, \<gamma>, \<theta>, def, \<tau>)" and
    ex1: "t, \<sigma>, \<gamma>, \<theta>, def \<turnstile> < ss2, \<tau>> \<longrightarrow>\<^sub>s \<tau>'" and ci1: "context_invariant t \<sigma> \<gamma> \<theta> def \<tau>" and
    "tw = worldline2 t \<sigma> \<theta> def \<tau>" and "fst tw = t"
    using destruct_worldline_exist worldline2_constructible
    by (smt assms(2) fst_conv fst_destruct_worldline world_seq_exec_cases)
  have beval: "t , \<sigma> , \<gamma> , \<theta>, def  \<turnstile> g \<longrightarrow>\<^sub>b Bv False"
    by (metis \<open>tw = worldline2 t \<sigma> \<theta> def \<tau>\<close> assms(1) beval_beval_world_raw_ci beval_world_raw2_def
    ci1 des1 destruct_worldline_ensure_non_stuttering_hist_raw fst_conv sndI worldline2_def)
  have "worldline2 t \<sigma> \<theta> def \<tau>' = tw'"
    by (smt Pair_inject assms(2) b_seq_exec_deterministic des1 ex1 world_seq_exec_cases)
  thus ?thesis
    apply (intro world_seq_exec.intros)
      apply (rule des1)
     apply (intro b_seq_exec.intros(4))
      apply (intro beval)
     apply (rule ex1)
    apply assumption
    done
qed

lemma world_seq_exec_trans:
  assumes "beval_world_raw2 tw exp x"
  assumes "tw' = tw[sig, dly :=\<^sub>2 x]"
  assumes "0 < dly"
  shows   "tw, Bassign_trans sig exp dly \<Rightarrow>\<^sub>s tw'"
proof -
  obtain t \<sigma> \<gamma> \<theta> def where t_def: "t = fst tw" and  \<sigma>_def: "\<sigma> = state_of_world (snd tw) t" and
    \<gamma>_def: "\<gamma> = event_of_world (snd tw) t" and  \<theta>_def: "\<theta> = derivative_hist_raw (snd tw) t" and
    def_def: "def = (fst o snd) tw" and beval: "t, \<sigma>, \<gamma>, \<theta>, def \<turnstile> exp \<longrightarrow>\<^sub>b x"
    using assms(1)   by (simp add: beval_world_raw.simps beval_world_raw2_def)
  obtain \<gamma>' \<tau> where "destruct_worldline tw = (t, \<sigma>, \<gamma>', \<theta>, def, \<tau>)" and
    \<gamma>'_def: "\<gamma>' = {s. snd (snd tw) s (fst tw) \<noteq> signal_of (fst (snd tw) s) (derivative_hist_raw (snd tw) (fst tw)) s (fst tw - 1)}" and
    "\<tau>  = derivative_raw (snd tw) (fst tw)"
    unfolding destruct_worldline_def Let_def t_def \<sigma>_def state_of_world_def def_def \<theta>_def by auto
  have "\<gamma> = \<gamma>'"
  proof (cases "t = 0")
    case True
    hence "\<gamma> =  {s. snd (snd tw) s t \<noteq> fst (snd tw) s}"
      unfolding \<gamma>_def event_of_world_def by auto
    have "derivative_hist_raw (snd tw) t = 0"
      unfolding derivative_hist_raw_def True zero_fun_def zero_option_def by auto
    hence "\<And>s. signal_of (fst (snd tw) s) (derivative_hist_raw (snd tw) t) s (t - 1) = (fst (snd tw) s)"
      using signal_of_empty by fastforce
    then show ?thesis
      unfolding \<gamma>_def \<gamma>'_def event_of_world_def sym[OF t_def] True by auto
  next
    case False
    hence "\<gamma> = {s. snd (snd tw) s t \<noteq> snd (snd tw) s (t - 1)}"
      unfolding \<gamma>_def event_of_world_def by auto
    have "\<And>s. signal_of (get_time (snd tw) s) (derivative_hist_raw (snd tw) t) s (t - 1) = snd (snd tw) s (t - 1)"
      using signal_of_derivative_hist_raw2
      by (metis False le_0_eq not_le_imp_less signal_of_derivative_hist_raw)
    then show ?thesis
      unfolding \<gamma>_def \<gamma>'_def event_of_world_def sym[OF t_def] using False
      by auto
  qed
  hence "destruct_worldline tw = (t, \<sigma>, \<gamma>, \<theta>, def, \<tau>)"
    using \<open>destruct_worldline tw = (t, \<sigma>, \<gamma>', \<theta>, def, \<tau>)\<close> by blast
  obtain \<tau>' where "t, \<sigma>, \<gamma>, \<theta>, def \<turnstile> <Bassign_trans sig exp dly, \<tau>> \<longrightarrow>\<^sub>s \<tau>'" and "trans_post_raw sig x (\<sigma> sig) \<tau> t dly = \<tau>'"
    using b_seq_exec.intros(5) beval by fastforce
  hence "worldline2 t \<sigma> \<theta> def \<tau>' = tw'"
    by (metis \<open>\<gamma> = \<gamma>'\<close> \<open>destruct_worldline tw = (t, \<sigma>, \<gamma>', \<theta>, def, \<tau>)\<close> assms(2) assms(3) beval
    beval_beval_world_raw_ci beval_raw_deterministic beval_world_raw2_def
    destruct_worldline_ensure_non_stuttering_hist_raw lift_world_trans_worldline_upd2 snd_conv t_def
    world_seq_exec.intros worldline2_constructible worldline2_def)
  thus ?thesis
    by (meson \<open>destruct_worldline tw = (t, \<sigma>, \<gamma>, \<theta>, def, \<tau>)\<close> \<open>t , \<sigma> , \<gamma> , \<theta>, def \<turnstile> <Bassign_trans
    sig exp dly , \<tau>> \<longrightarrow>\<^sub>s \<tau>'\<close> world_seq_exec.intros)
qed

lemma world_seq_exec_inert:
  assumes "beval_world_raw2 tw exp x"
  assumes "tw' = tw\<lbrakk>sig, dly :=\<^sub>2 x\<rbrakk>"
  assumes "0 < dly"
  shows   "tw, Bassign_inert sig exp dly \<Rightarrow>\<^sub>s tw'"
proof -
  obtain t \<sigma> \<gamma> \<theta> def where t_def: "t = fst tw" and  \<sigma>_def: "\<sigma> = state_of_world (snd tw) t" and
    \<gamma>_def: "\<gamma> = event_of_world (snd tw) t" and  \<theta>_def: "\<theta> = derivative_hist_raw (snd tw) t" and
    def_def: "def = (fst o snd) tw" and beval: "t, \<sigma>, \<gamma>, \<theta>, def \<turnstile> exp \<longrightarrow>\<^sub>b x"
    using assms(1)   by (simp add: beval_world_raw.simps beval_world_raw2_def)
  obtain \<gamma>' \<tau> where "destruct_worldline tw = (t, \<sigma>, \<gamma>', \<theta>, def, \<tau>)" and
    \<gamma>'_def: "\<gamma>' = {s. snd (snd tw) s (fst tw) \<noteq> signal_of (fst (snd tw) s) (derivative_hist_raw (snd tw) (fst tw)) s (fst tw - 1)}" and
    "\<tau>  = derivative_raw (snd tw) (fst tw)"
    unfolding destruct_worldline_def Let_def t_def \<sigma>_def state_of_world_def def_def \<theta>_def by auto
  have "\<gamma> = \<gamma>'"
  proof (cases "t = 0")
    case True
    hence "\<gamma> =  {s. snd (snd tw) s t \<noteq> fst (snd tw) s}"
      unfolding \<gamma>_def event_of_world_def by auto
    have "derivative_hist_raw (snd tw) t = 0"
      unfolding derivative_hist_raw_def True zero_fun_def zero_option_def by auto
    hence "\<And>s. signal_of (fst (snd tw) s) (derivative_hist_raw (snd tw) t) s (t - 1) = (fst (snd tw) s)"
      using signal_of_empty by fastforce
    then show ?thesis
      unfolding \<gamma>_def \<gamma>'_def event_of_world_def sym[OF t_def] True by auto
  next
    case False
    hence "\<gamma> = {s. snd (snd tw) s t \<noteq> snd (snd tw) s (t - 1)}"
      unfolding \<gamma>_def event_of_world_def by auto
    have "\<And>s. signal_of (get_time (snd tw) s) (derivative_hist_raw (snd tw) t) s (t - 1) = snd (snd tw) s (t - 1)"
      using signal_of_derivative_hist_raw2
      by (metis False le_0_eq not_le_imp_less signal_of_derivative_hist_raw)
    then show ?thesis
      unfolding \<gamma>_def \<gamma>'_def event_of_world_def sym[OF t_def] using False
      by auto
  qed
  hence "destruct_worldline tw = (t, \<sigma>, \<gamma>, \<theta>, def, \<tau>)"
    using \<open>destruct_worldline tw = (t, \<sigma>, \<gamma>', \<theta>, def, \<tau>)\<close> by blast
  obtain \<tau>' where "t, \<sigma>, \<gamma>, \<theta>, def \<turnstile> <Bassign_inert sig exp dly, \<tau>> \<longrightarrow>\<^sub>s \<tau>'" and "inr_post_raw sig x (\<sigma> sig) \<tau> t dly = \<tau>'"
    using b_seq_exec.intros(6) beval by fastforce
  hence "worldline2 t \<sigma> \<theta> def \<tau>' = tw'"
    by (metis \<open>\<gamma> = \<gamma>'\<close> \<open>destruct_worldline tw = (t, \<sigma>, \<gamma>', \<theta>, def, \<tau>)\<close> assms(1) assms(2) assms(3)
    beval_world_raw2_def destruct_worldline_ensure_non_stuttering
    destruct_worldline_ensure_non_stuttering_hist_raw lift_inr_post_worldline_upd snd_conv t_def
    worldline2_constructible worldline2_def worldline_inert_upd2_def)
  thus ?thesis
    by (meson \<open>destruct_worldline tw = (t, \<sigma>, \<gamma>, \<theta>, def, \<tau>)\<close> \<open>t , \<sigma> , \<gamma> , \<theta>, def \<turnstile> <Bassign_inert
    sig exp dly , \<tau>> \<longrightarrow>\<^sub>s \<tau>'\<close> world_seq_exec.intros)
qed

inductive world_seq_exec_alt :: "nat \<times> 'signal worldline_init \<Rightarrow> 'signal seq_stmt \<Rightarrow> nat \<times> 'signal worldline_init \<Rightarrow> bool" where
  "world_seq_exec_alt tw Bnull tw"

| "world_seq_exec_alt tw ss1 tw'' \<Longrightarrow> world_seq_exec_alt tw'' ss2  tw' \<Longrightarrow> world_seq_exec_alt tw (Bcomp ss1 ss2) tw'"

| "beval_world_raw2 tw g (Bv True) \<Longrightarrow> world_seq_exec_alt tw ss1 tw' \<Longrightarrow> world_seq_exec_alt tw (Bguarded g ss1 ss2) tw'"

| "beval_world_raw2 tw g (Bv False) \<Longrightarrow> world_seq_exec_alt tw ss2 tw' \<Longrightarrow> world_seq_exec_alt tw (Bguarded g ss1 ss2) tw'"

| "beval_world_raw2 tw exp x \<Longrightarrow> tw' = tw[sig, dly :=\<^sub>2 x] \<Longrightarrow> world_seq_exec_alt tw (Bassign_trans sig exp dly) tw'"

| "beval_world_raw2 tw exp x \<Longrightarrow> tw' = tw\<lbrakk> sig, dly :=\<^sub>2 x\<rbrakk> \<Longrightarrow> world_seq_exec_alt tw (Bassign_inert sig exp dly) tw'"

| "beval_world_raw2 tw exp x \<Longrightarrow> beval_world_raw2 tw exp' x \<Longrightarrow> world_seq_exec_alt tw ss tw' \<Longrightarrow> world_seq_exec_alt tw (Bcase exp ((Explicit exp', ss) # choices)) tw'"

| "beval_world_raw2 tw exp x \<Longrightarrow> beval_world_raw2 tw exp' x' \<Longrightarrow> x \<noteq> x' \<Longrightarrow> world_seq_exec_alt tw (Bcase exp choices) tw' \<Longrightarrow> world_seq_exec_alt tw (Bcase exp ((Explicit exp', ss) # choices)) tw'"

| "world_seq_exec_alt tw ss tw' \<Longrightarrow> world_seq_exec_alt tw (Bcase exp ((Others, ss) # choices)) tw'"

| "world_seq_exec_alt tw (Bcase exp []) tw"

lemma world_seq_exec_alt_imp_world_seq_exec:
  assumes "world_seq_exec_alt tw ss tw'"
  assumes "nonneg_delay ss"
  shows   "tw, ss \<Rightarrow>\<^sub>s tw'"
  using assms
proof (induction rule:world_seq_exec_alt.induct)
  case (7 tw exp x exp' ss tw' choices)
  hence "tw, ss \<Rightarrow>\<^sub>s tw'"
    unfolding nonneg_delay.simps by auto
  obtain t \<sigma> \<gamma> \<theta> def \<tau> \<tau>' where des: "destruct_worldline tw = (t, \<sigma>, \<gamma>, \<theta>, def, \<tau>)" and
                                exe: "b_seq_exec t \<sigma> \<gamma> \<theta> def ss \<tau> \<tau>'" and
                                con: "worldline2 t \<sigma> \<theta> def \<tau>' = tw'"
    by (rule world_seq_exec_cases[OF \<open>tw, ss \<Rightarrow>\<^sub>s tw'\<close>])
  have " t , \<sigma> , \<gamma> , \<theta>, def  \<turnstile> exp \<longrightarrow>\<^sub>b x" and "t , \<sigma> , \<gamma> , \<theta>, def  \<turnstile> exp' \<longrightarrow>\<^sub>b x"
    using 7(1) 7(2) unfolding beval_world_raw2_def
    by (metis (full_types) beval_beval_world_raw_ci des
    destruct_worldline_ensure_non_stuttering_hist_raw fst_conv snd_conv worldline2_constructible
    worldline2_def)+
  hence "b_seq_exec t \<sigma> \<gamma> \<theta> def (Bcase exp ((Explicit exp', ss) # choices)) \<tau> \<tau>'"
    using exe by (intro b_seq_exec.intros)
  thus ?case
    using des con by (intro world_seq_exec.intros)
next
  case (8 tw exp x exp' x' choices tw' ss)
  hence "tw, Bcase exp choices \<Rightarrow>\<^sub>s tw'"
    unfolding nonneg_delay.simps by auto
  obtain t \<sigma> \<gamma> \<theta> def \<tau> \<tau>' where des: "destruct_worldline tw = (t, \<sigma>, \<gamma>, \<theta>, def, \<tau>)" and
                                exe: "b_seq_exec t \<sigma> \<gamma> \<theta> def (Bcase exp choices) \<tau> \<tau>'" and
                                con: "worldline2 t \<sigma> \<theta> def \<tau>' = tw'"
    by (rule world_seq_exec_cases[OF \<open>tw, Bcase exp choices \<Rightarrow>\<^sub>s tw'\<close>])
  have " t , \<sigma> , \<gamma> , \<theta>, def  \<turnstile> exp \<longrightarrow>\<^sub>b x" and "t , \<sigma> , \<gamma> , \<theta>, def  \<turnstile> exp' \<longrightarrow>\<^sub>b x'"
    using 8(1) 8(2) unfolding beval_world_raw2_def
    by (metis (full_types) beval_beval_world_raw_ci des
    destruct_worldline_ensure_non_stuttering_hist_raw fst_conv snd_conv worldline2_constructible
    worldline2_def)+
  hence "b_seq_exec t \<sigma> \<gamma> \<theta> def (Bcase exp ((Explicit exp', ss) # choices)) \<tau> \<tau>'"
    using exe \<open>x \<noteq> x'\<close> by (intro b_seq_exec.intros(8))
  then show ?case
    using des con by (intro world_seq_exec.intros)
next
  case (9 tw ss tw' exp choices)
  then show ?case
    by (smt b_seq_exec.intros(9) list.simps(9) list_all_simps(1) nonneg_delay.simps(6) prod.sel(2)
    world_seq_exec.intros world_seq_exec_cases)
next
  case (10 tw exp)
  then show ?case
    by (metis (no_types, lifting) b_seq_exec.intros(10) destruct_worldline_def world_seq_exec.intros
    worldline2_constructible)
qed (auto simp add: world_seq_exec_bnull world_seq_exec_comp world_seq_exec_guarded
     world_seq_exec_guarded_not world_seq_exec_trans world_seq_exec_inert)

lemma world_seq_exec_imp_world_seq_exec_alt:
  assumes "tw, ss \<Rightarrow>\<^sub>s tw'"
  assumes "nonneg_delay ss"
  shows   "world_seq_exec_alt tw ss tw'"
  using assms
proof (induction rule:world_seq_exec.induct)
  case (1 tw t \<sigma> \<gamma> \<theta> def \<tau> s \<tau>' tw')
  show ?case
    using 1(2) 1(1) 1(3-4)
  proof (induction arbitrary: tw tw' rule: b_seq_exec.inducts)
    case (1 t \<sigma> \<gamma> \<theta> def \<tau>)
    then show ?case
      using world_seq_exec_alt.intros(1) worldline2_constructible by blast
  next
    case (2 t \<sigma> \<gamma> \<theta> def s1 \<tau> \<tau>'' s2 \<tau>')
    note prems = "2.prems"
    obtain tw'' where tw''_def: " tw'' = worldline2 t \<sigma> \<theta> def \<tau>''" and "world_seq_exec_alt tw s1 tw''"
      using "2.IH"(1)[OF prems(1)] prems(3) unfolding nonneg_delay.simps by auto
    have des2: "destruct_worldline tw'' = (t, \<sigma>, \<gamma>, \<theta>, def, \<tau>'')"
      unfolding tw''_def
    proof (rule destruct_worldline_correctness3)
      show "context_invariant t \<sigma> \<gamma> \<theta> def \<tau>''"
        using prems(1) \<open>nonneg_delay (Bcomp s1 s2)\<close> \<open>t , \<sigma> , \<gamma> , \<theta>, def \<turnstile> < s1 , \<tau>> \<longrightarrow>\<^sub>s \<tau>''\<close>
        b_seq_exec_preserves_context_invariant worldline2_constructible
        unfolding nonneg_delay.simps by blast
    next
      have "\<forall>s. non_stuttering (to_trans_raw_sig \<tau>) \<sigma> s"
        using destruct_worldline_ensure_non_stuttering  using prems(1) by blast
      thus "\<forall>s. non_stuttering (to_trans_raw_sig \<tau>'') \<sigma> s"
        by (meson "2.hyps"(1) b_seq_exec_preserves_non_stuttering
        destruct_worldline_trans_zero_upto_now nonneg_delay.simps(2) prems(1) prems(3))
    next
      show "\<forall>s. non_stuttering (to_trans_raw_sig \<theta>) def s"
        using prems(1) destruct_worldline_ensure_non_stuttering_hist_raw by blast
    qed
    have " t , \<sigma> , \<gamma> , \<theta>, def  \<turnstile> < s2 , \<tau>''> \<longrightarrow>\<^sub>s \<tau>'"
      using \<open>t , \<sigma> , \<gamma> , \<theta>, def \<turnstile> < s1 , \<tau>> \<longrightarrow>\<^sub>s \<tau>''\<close> b_seq_exec_deterministic "2.hyps"(2)
      by blast
    have "world_seq_exec_alt tw'' s2 (worldline2 t \<sigma> \<theta> def \<tau>')"
      using "2.IH"(2)[OF des2] prems(3) by auto
    then show ?case
      using \<open>world_seq_exec_alt tw s1 tw''\<close> prems(2) world_seq_exec_alt.intros(2) by blast
  next
    case (3 t \<sigma> \<gamma> \<theta> def x1 s1 \<tau> \<tau>' s2)
    hence "t , \<sigma> , \<gamma> , \<theta>, def  \<turnstile> < s1 , \<tau>> \<longrightarrow>\<^sub>s \<tau>'"
      using \<open>t , \<sigma> , \<gamma> , \<theta>, def \<turnstile> x1 \<longrightarrow>\<^sub>b Bv True\<close>  by (metis)
    thus ?case
      by (metis "3.IH" "3.prems"
      \<open>t , \<sigma> , \<gamma> , \<theta>, def \<turnstile> x1 \<longrightarrow>\<^sub>b Bv True\<close> beval_beval_world_raw_ci beval_world_raw2_def
      destruct_worldline_ensure_non_stuttering_hist_raw fst_conv nonneg_delay.simps(3) snd_conv
      world_seq_exec_alt.intros(3) worldline2_constructible worldline2_def)
  next
    case (4 t \<sigma> \<gamma> \<theta> def x1 s2 \<tau> \<tau>' s1)
    hence "t, \<sigma>, \<gamma>, \<theta>, def \<turnstile> < s2, \<tau>> \<longrightarrow>\<^sub>s \<tau>'"
      using \<open>t , \<sigma> , \<gamma> , \<theta>, def \<turnstile> x1 \<longrightarrow>\<^sub>b Bv False\<close> by (metis)
    thus ?case
      by (metis "4.IH" "4.prems" \<open>t , \<sigma> , \<gamma> , \<theta>, def \<turnstile> x1 \<longrightarrow>\<^sub>b Bv False\<close> beval_beval_world_raw_ci beval_world_raw2_def
      destruct_worldline_ensure_non_stuttering_hist_raw fst_conv nonneg_delay.simps(3) snd_conv
      world_seq_exec_alt.intros(4) worldline2_constructible worldline2_def)
  next
    case (5 t \<sigma> \<gamma> \<theta> def e x sig \<tau> dly \<tau>')
    then show ?case
      by (metis b_seq_exec.intros(5) lift_world_trans_worldline_upd2 nonneg_delay.simps(4)
      world_seq_exec.intros world_seq_exec_alt.intros(5))
  next
    case (6 t \<sigma> \<gamma> \<theta> def e x sig \<tau> dly \<tau>')
    then show ?case
      by (metis b_seq_exec.intros(6) lift_world_inert_worldline_upd2 nonneg_delay.simps(5)
      world_seq_exec.intros world_seq_exec_alt.intros(6))
  next
    case (7 t \<sigma> \<gamma> \<theta> def exp x exp' ss \<tau> \<tau>' choices)
    hence "world_seq_exec_alt tw ss tw'"
      unfolding nonneg_delay.simps by auto
    have "state_of_world (snd tw) (get_time tw) = \<sigma>"
      using "7.prems" unfolding destruct_worldline_def Let_def state_of_world_def by auto
    moreover have "derivative_hist_raw (snd tw) (get_time tw) = \<theta>"
      using "7.prems" unfolding destruct_worldline_def Let_def by auto
    moreover have "event_of_world (snd tw) (get_time tw) = \<gamma>"
    proof (cases "0 < fst tw")
      case True
      fix s
      have "snd (snd tw) s t = \<sigma> s"
        using `state_of_world (snd tw) (fst tw) = \<sigma>` unfolding state_of_world_def
        by (metis "7.prems"(1) fst_conv fst_destruct_worldline)
      moreover have "snd (snd tw) s (fst tw - 1) = signal_of (def s) \<theta> s (fst tw - 1)"
        unfolding worldline_raw_def using True
        by (metis (mono_tags, lifting) "7.prems"(1) \<open>derivative_hist_raw (snd tw) (get_time tw) = \<theta>\<close>
        destruct_worldline_correctness(6) destruct_worldline_def diff_less
        signal_of_derivative_hist_raw worldline2_constructible zero_less_one)
      ultimately show ?thesis
        unfolding event_of_world_def
        using True
        by (metis (mono_tags, lifting) "7.prems"(1) Collect_cong Pair_inject destruct_worldline_def
        diff_less less_numeral_extra(3) signal_of_derivative_hist_raw zero_less_one)
    next
      case False
      hence "fst tw = 0" by auto
      hence ev: "event_of_world (snd tw) (fst tw) = {s. snd (snd tw) s 0 \<noteq> def s}"
        unfolding event_of_world_def
        by (metis (mono_tags, lifting) "7.prems"(1) Collect_cong destruct_worldline_correctness(6)
        destruct_worldline_def worldline2_constructible)
      have \<gamma>_def': "\<gamma> = {s. \<sigma> s \<noteq> signal_of (def s) \<theta> s 0}"
        using `fst tw = 0`
        by (metis (no_types, lifting) "7.prems"(1) Collect_cong One_nat_def calculation(2)
        destruct_worldline_correctness(2) destruct_worldline_correctness(3)
        destruct_worldline_correctness(6) destruct_worldline_def diff_is_0_eq' le_add2 plus_1_eq_Suc
        worldline2_constructible)
      have "\<theta> = 0"
        unfolding `fst tw = 0` zero_fun_def
        by (metis \<open>get_time tw = 0\<close> calculation(2) derivative_hist_raw_def zero_option_def
        zero_order(1))
      hence "\<And>s. signal_of (def s) \<theta> s 0 = def s"
        using signal_of_empty by metis
      hence "\<gamma> = {s. \<sigma> s \<noteq> def s}"
        using \<gamma>_def' by auto
      moreover have "\<And>s.  snd (snd tw) s 0 = \<sigma> s"
        using `state_of_world (snd tw) (fst tw) = \<sigma>` `fst tw = 0` unfolding state_of_world_def by auto
      ultimately  have "\<gamma> = {s. snd (snd tw) s 0 \<noteq> def s}"
        by auto
      thus ?thesis  using ev by auto
    qed
    ultimately have "beval_world_raw2 tw exp x"
      unfolding beval_world_raw2_def
      by (metis (mono_tags, lifting) "7.hyps"(1) "7.prems"(1) beval_world_raw.simps
          destruct_worldline_def old.prod.inject)
    have "beval_world_raw2 tw exp' x"
      unfolding beval_world_raw2_def
      by (metis (mono_tags, lifting) "7.hyps"(2) "7.prems"(1) Pair_inject \<open>event_of_world (snd tw)
      (get_time tw) = \<gamma>\<close> \<open>state_of_world (snd tw) (get_time tw) = \<sigma>\<close> beval_world_raw.simps
      destruct_worldline_def)
    thus ?case
      using \<open>beval_world_raw2 tw exp x\<close> \<open>world_seq_exec_alt tw ss tw'\<close> world_seq_exec_alt.intros(7)
      by blast
  next
    case (8 t \<sigma> \<gamma> \<theta> def exp x exp' x' choices \<tau> \<tau>' ss)
    hence "world_seq_exec_alt tw (Bcase exp choices) tw'"
      unfolding nonneg_delay.simps by auto
    have "state_of_world (snd tw) (get_time tw) = \<sigma>"
      using "8.prems" unfolding destruct_worldline_def Let_def state_of_world_def by auto
    have "derivative_hist_raw (snd tw) (get_time tw) = \<theta>"
      using "8.prems" unfolding destruct_worldline_def Let_def by auto
    have "event_of_world (snd tw) (get_time tw) = \<gamma>"
    proof (cases "0 < fst tw")
      case True
      fix s
      have "snd (snd tw) s t = \<sigma> s"
        using `state_of_world (snd tw) (fst tw) = \<sigma>` unfolding state_of_world_def
        by (metis "8.prems"(1) fst_conv fst_destruct_worldline)
      moreover have "snd (snd tw) s (fst tw - 1) = signal_of (def s) \<theta> s (fst tw - 1)"
        unfolding worldline_raw_def using True
        by (metis (mono_tags, lifting) "8.prems"(1) \<open>derivative_hist_raw (snd tw) (get_time tw) = \<theta>\<close>
        destruct_worldline_correctness(6) destruct_worldline_def diff_less
        signal_of_derivative_hist_raw worldline2_constructible zero_less_one)
      ultimately show ?thesis
        unfolding event_of_world_def
        using True
        by (metis (mono_tags, lifting) "8.prems"(1) Collect_cong Pair_inject destruct_worldline_def
        diff_less less_numeral_extra(3) signal_of_derivative_hist_raw zero_less_one)
    next
      case False
      hence "fst tw = 0" by auto
      hence ev: "event_of_world (snd tw) (fst tw) = {s. snd (snd tw) s 0 \<noteq> def s}"
        unfolding event_of_world_def
        by (metis (mono_tags, lifting) "8.prems"(1) Collect_cong destruct_worldline_correctness(6)
        destruct_worldline_def worldline2_constructible)
      have \<gamma>_def': "\<gamma> = {s. \<sigma> s \<noteq> signal_of (def s) \<theta> s 0}"
        using `fst tw = 0`
        by (metis (no_types, lifting) "8.prems"(1) Collect_cong One_nat_def
        \<open>derivative_hist_raw (snd tw) (get_time tw) = \<theta>\<close>
        destruct_worldline_correctness(2) destruct_worldline_correctness(3)
        destruct_worldline_correctness(6) destruct_worldline_def diff_is_0_eq' le_add2 plus_1_eq_Suc
        worldline2_constructible)
      have "\<theta> = 0"
        unfolding `fst tw = 0` zero_fun_def
        by (metis \<open>get_time tw = 0\<close> \<open>derivative_hist_raw (snd tw) (get_time tw) = \<theta>\<close>
        derivative_hist_raw_def zero_option_def zero_order(1))
      hence "\<And>s. signal_of (def s) \<theta> s 0 = def s"
        using signal_of_empty by metis
      hence "\<gamma> = {s. \<sigma> s \<noteq> def s}"
        using \<gamma>_def' by auto
      moreover have "\<And>s.  snd (snd tw) s 0 = \<sigma> s"
        using `state_of_world (snd tw) (fst tw) = \<sigma>` `fst tw = 0` unfolding state_of_world_def by auto
      ultimately  have "\<gamma> = {s. snd (snd tw) s 0 \<noteq> def s}"
        by auto
      thus ?thesis  using ev by auto
    qed
    have "beval_world_raw2 tw exp x"
      unfolding beval_world_raw2_def
      by (metis (no_types, lifting) "8.hyps"(1) "8.prems"(1) \<open>derivative_hist_raw (snd tw) (get_time
      tw) = \<theta>\<close> \<open>event_of_world (snd tw) (get_time tw) = \<gamma>\<close> \<open>state_of_world (snd tw) (get_time tw) =
      \<sigma>\<close> beval_world_raw.intros destruct_worldline_correctness(6) destruct_worldline_def fst_conv
      worldline2_constructible)
    have "beval_world_raw2 tw exp' x'"
      unfolding beval_world_raw2_def
      by (metis (no_types, lifting) "8.hyps"(2) "8.prems"(1) \<open>derivative_hist_raw (snd tw) (get_time
      tw) = \<theta>\<close> \<open>event_of_world (snd tw) (get_time tw) = \<gamma>\<close> \<open>state_of_world (snd tw) (get_time tw) =
      \<sigma>\<close> beval_world_raw.intros destruct_worldline_correctness(6) destruct_worldline_def fst_conv
      worldline2_constructible)
    then show ?case
      using "8.hyps"(3) \<open>beval_world_raw2 tw exp x\<close> \<open>world_seq_exec_alt tw (Bcase exp choices) tw'\<close>
      world_seq_exec_alt.intros(8) by blast
  next
    case (9 t \<sigma> \<gamma> \<theta> def ss \<tau> \<tau>' exp choices)
    then show ?case
      by (simp add: world_seq_exec_alt.intros(9))
  next
    case (10 t \<sigma> \<gamma> \<theta> def exp \<tau>)
    then show ?case
      using world_seq_exec_alt.intros(10) worldline2_constructible by blast
  qed
qed

lemma world_seq_exec_alt_def:
  assumes "nonneg_delay ss"
  shows "world_seq_exec_alt tw ss = world_seq_exec tw ss"
proof (rule, rule)
  fix x
  assume "world_seq_exec_alt tw ss x"
  thus "tw, ss \<Rightarrow>\<^sub>s x"
    using world_seq_exec_alt_imp_world_seq_exec assms by blast
next
  fix x
  assume "tw, ss \<Rightarrow>\<^sub>s x"
  thus "world_seq_exec_alt tw ss x"
    using world_seq_exec_imp_world_seq_exec_alt assms by blast
qed

inductive_cases world_seq_exec_alt_cases [elim!] :
  "world_seq_exec_alt tw Bnull ss"
  "world_seq_exec_alt tw (Bcomp ss1 ss2) ss"
  "world_seq_exec_alt tw (Bguarded g ss1 ss2) ss"
  "world_seq_exec_alt tw (Bassign_trans sig exp dly) ss"
  "world_seq_exec_alt tw (Bassign_inert sig exp dly) ss"

lemma world_seq_exec_bcase_empty:
  "tw, Bcase exp [] \<Rightarrow>\<^sub>s tw"
proof -
  have "world_seq_exec_alt tw (Bcase exp []) tw"
    by (auto intro!: world_seq_exec_alt.intros)
  moreover have "nonneg_delay (Bcase exp [])"
    by auto
  ultimately show ?thesis
    using world_seq_exec_alt_imp_world_seq_exec  by blast
qed

lemma world_seq_exec_bcase_others:
  fixes tw :: "nat \<times> 'a worldline_init"
  assumes "tw, ss \<Rightarrow>\<^sub>s tw'"
  shows   "world_seq_exec tw (Bcase exp ((Others, ss) # choices)) tw'"
proof -
  obtain t \<sigma> \<gamma> \<theta> \<tau> \<tau>' def where des1: "destruct_worldline tw = (t, \<sigma>, \<gamma>, \<theta>, def, \<tau>)" and
    ex1: "t, \<sigma>, \<gamma>, \<theta>, def \<turnstile> < ss, \<tau>> \<longrightarrow>\<^sub>s \<tau>'" and ci1: "context_invariant t \<sigma> \<gamma> \<theta> def \<tau>" and
    "tw = worldline2 t \<sigma> \<theta> def \<tau>" and "fst tw = t"
    using destruct_worldline_exist worldline2_constructible
    by (smt assms fst_conv fst_destruct_worldline world_seq_exec_cases)
  hence "t, \<sigma>, \<gamma>, \<theta>, def \<turnstile> < Bcase exp ((Others, ss) # choices), \<tau>> \<longrightarrow>\<^sub>s \<tau>'"
    by (simp add: b_seq_exec.intros(9))
  thus ?thesis
    by (smt Pair_inject assms b_seq_exec_deterministic des1 ex1 world_seq_exec.intros
    world_seq_exec_cases)
qed

definition wp :: "'signal seq_stmt \<Rightarrow> 'signal assn2 \<Rightarrow> 'signal assn2" where
  "wp ss Q = (\<lambda>tw. \<forall>tw'. (tw, ss \<Rightarrow>\<^sub>s tw') \<longrightarrow> Q tw')"

lemma wp_bnull:
  "wp Bnull Q = Q"
  apply (rule ext)
  by (metis (full_types) nonneg_delay.simps(1) world_seq_exec_alt_cases(1) world_seq_exec_alt_def
  world_seq_exec_bnull wp_def)

lemma wp_bcomp:
  "nonneg_delay (Bcomp ss1 ss2) \<Longrightarrow> wp (Bcomp ss1 ss2) Q = wp ss1 (wp ss2 Q)"
  apply (rule ext)
  unfolding wp_def
  by (meson nonneg_delay.simps(2) world_seq_exec_alt_cases(2) world_seq_exec_alt_imp_world_seq_exec
  world_seq_exec_comp world_seq_exec_imp_world_seq_exec_alt)

lemma wp_guarded:
  "wp (Bguarded g ss1 ss2) Q =
  (\<lambda>tw. (\<forall>x. beval_world_raw2 tw g x \<and> is_Bv x \<longrightarrow> (if bval_of x then wp ss1 Q tw else wp ss2 Q tw)))"
  apply (rule ext)
  unfolding wp_def
  by (smt beval_beval_world_raw_ci beval_world_raw2_def
  destruct_worldline_ensure_non_stuttering_hist_raw prod.sel(1) seq_cases_bguarded snd_conv
  val.collapse(1) val.discI(1) val.inject(1) world_seq_exec.intros world_seq_exec_cases
  world_seq_exec_guarded world_seq_exec_guarded_not worldline2_constructible worldline2_def)

lemma wp_bcase_empty:
  "wp (Bcase exp []) Q = Q"
  apply (rule ext)
  unfolding wp_def using world_seq_exec_bcase_empty world_seq_exec_deterministic
  by blast

lemma wp_bcase_others:
  "wp (Bcase exp ((Others, ss) # choices)) Q = wp ss Q"
  apply (rule ext)
  unfolding wp_def
  using bcase_others_tw_elim world_seq_exec_bcase_others by blast

lemma wp_guarded':
  "wp (Bguarded g ss1 ss2) Q =
  (\<lambda>tw. (beval_world_raw2 tw g (Bv True) \<longrightarrow> wp ss1 Q tw) \<and> (beval_world_raw2 tw g (Bv False) \<longrightarrow> wp ss2 Q tw))"
  apply (rule ext)
  unfolding wp_def
  by (smt beval_beval_world_raw_ci beval_world_raw2_def
  destruct_worldline_ensure_non_stuttering_hist_raw fst_conv seq_cases_bguarded snd_conv
  world_seq_exec.intros world_seq_exec_cases world_seq_exec_guarded world_seq_exec_guarded_not
  worldline2_constructible worldline2_def)

lemma wp_bcase_explicit:
  "wp (Bcase exp ((Explicit exp', ss) # choices)) Q =
  (\<lambda>tw. (\<forall>x x'. beval_world_raw2 tw exp x \<and> beval_world_raw2 tw exp' x' \<longrightarrow> (if x = x' then wp ss Q tw else wp (Bcase exp choices) Q tw)))"
  apply (rule ext)
  unfolding wp_def
proof (rule)+
  fix tw x x'
  assume *: "\<forall>tw'. tw, Bcase exp ((Explicit exp', ss) # choices) \<Rightarrow>\<^sub>s tw' \<longrightarrow> Q tw'"
  assume "beval_world_raw2 tw exp x \<and> beval_world_raw2 tw exp' x'"
  have "x = x' \<or> x \<noteq> x'"
    by auto
  moreover
  { assume "x = x'"
    { fix tw'
      assume "tw, ss \<Rightarrow>\<^sub>s tw'"
      hence  "tw, Bcase exp ((Explicit exp', ss) # choices) \<Rightarrow>\<^sub>s tw'"
        using \<open>beval_world_raw2 tw exp x \<and> beval_world_raw2 tw exp' x'\<close> \<open>x = x'\<close>
        world_seq_exec_explicit_match by blast
      with * have "Q tw'"
        by blast }
    hence "\<forall>tw'. tw, ss \<Rightarrow>\<^sub>s tw' \<longrightarrow> Q tw'"
      by blast }
  moreover
  { assume "x \<noteq> x'"
    { fix tw'
      assume "tw, Bcase exp choices \<Rightarrow>\<^sub>s tw'"
      hence  "tw, Bcase exp ((Explicit exp', ss) # choices) \<Rightarrow>\<^sub>s tw'"
        using \<open>beval_world_raw2 tw exp x \<and> beval_world_raw2 tw exp' x'\<close> \<open>x \<noteq> x'\<close>
        world_seq_exec_explicit_no_match by blast
      with * have "Q tw'"
        by blast }
    hence "\<forall>tw'. tw, Bcase exp choices \<Rightarrow>\<^sub>s tw' \<longrightarrow> Q tw'"
      by auto }
  ultimately show "if x = x' then \<forall>tw'. tw, ss \<Rightarrow>\<^sub>s tw' \<longrightarrow> Q tw' else \<forall>tw'. tw, Bcase exp choices \<Rightarrow>\<^sub>s tw' \<longrightarrow> Q tw'"
    by simp
next
  fix tw
  show "\<forall>x x'. beval_world_raw2 tw exp x \<and> beval_world_raw2 tw exp' x' \<longrightarrow>
                 (if x = x' then \<forall>tw'. tw, ss \<Rightarrow>\<^sub>s tw' \<longrightarrow> Q tw' else \<forall>tw'. tw, Bcase exp choices \<Rightarrow>\<^sub>s tw' \<longrightarrow> Q tw') \<Longrightarrow>
          \<forall>tw'. tw, Bcase exp ((Explicit exp', ss) # choices) \<Rightarrow>\<^sub>s tw' \<longrightarrow> Q tw'"
  proof (rule)+
    fix tw'
    assume *: "\<forall>x x'. beval_world_raw2 tw exp x \<and> beval_world_raw2 tw exp' x' \<longrightarrow>
                  (if x = x' then \<forall>tw'. tw, ss \<Rightarrow>\<^sub>s tw' \<longrightarrow> Q tw' else \<forall>tw'. tw, Bcase exp choices \<Rightarrow>\<^sub>s tw' \<longrightarrow> Q tw')"
    assume "tw, Bcase exp ((Explicit exp', ss) # choices) \<Rightarrow>\<^sub>s tw'"
    then obtain t \<sigma> \<gamma> \<theta> def \<tau> \<tau>' where
                                  des: "destruct_worldline tw = (t, \<sigma>, \<gamma>, \<theta>, def, \<tau>)" and
                                  exe: "b_seq_exec t \<sigma> \<gamma> \<theta> def (Bcase exp ((Explicit exp', ss) # choices)) \<tau> \<tau>'" and
                                  con: "worldline2 t \<sigma> \<theta> def \<tau>' = tw'"
      using world_seq_exec_cases by blast
    obtain x x' where bevalx: "t , \<sigma> , \<gamma> , \<theta>, def  \<turnstile> exp \<longrightarrow>\<^sub>b x" and bevalx': "t , \<sigma> , \<gamma> , \<theta>, def  \<turnstile> exp' \<longrightarrow>\<^sub>b x'"
      by (rule seq_cases_bcase[OF exe]) blast+
    (* TODO: factor this proof out *)
    have "beval_world_raw (snd tw) (fst tw) exp x"
    proof (intro beval_world_raw.intros)
      show " state_of_world (snd tw) (get_time tw) = \<sigma>"
        using des
        unfolding destruct_worldline_def Let_def state_of_world_def by auto
      show "derivative_hist_raw (snd tw) (fst tw) = \<theta>"
        using des
        unfolding destruct_worldline_def Let_def state_of_world_def by auto
      show "get_time tw , \<sigma> , \<gamma> , \<theta>, get_time (snd tw)  \<turnstile> exp \<longrightarrow>\<^sub>b x "
        by (metis (no_types, lifting) \<open>t , \<sigma> , \<gamma> , \<theta>, def \<turnstile> exp \<longrightarrow>\<^sub>b x\<close> des
        destruct_worldline_correctness(6) destruct_worldline_def fst_conv worldline2_constructible)
      show "event_of_world (snd tw) (fst tw) = \<gamma>"
      proof (cases "0 < fst tw")
        case True
        fix s
        have "snd (snd tw) s t = \<sigma> s"
          using `state_of_world (snd tw) (fst tw) = \<sigma>` unfolding state_of_world_def
          by (metis des fst_conv fst_destruct_worldline)
        moreover have "snd (snd tw) s (fst tw - 1) = signal_of (def s) \<theta> s (fst tw - 1)"
          unfolding worldline_raw_def using True
          by (metis (mono_tags, lifting) des \<open>derivative_hist_raw (snd tw) (get_time tw) = \<theta>\<close>
          destruct_worldline_correctness(6) destruct_worldline_def diff_less
          signal_of_derivative_hist_raw worldline2_constructible zero_less_one)
        ultimately show ?thesis
          unfolding event_of_world_def
          using True
          by (metis (mono_tags, lifting) des Collect_cong Pair_inject destruct_worldline_def
          diff_less less_numeral_extra(3) signal_of_derivative_hist_raw zero_less_one)
      next
        case False
        hence "fst tw = 0" by auto
        hence ev: "event_of_world (snd tw) (fst tw) = {s. snd (snd tw) s 0 \<noteq> def s}"
          unfolding event_of_world_def
          by (metis (mono_tags, lifting) des Collect_cong destruct_worldline_correctness(6)
          destruct_worldline_def worldline2_constructible)
        have \<gamma>_def': "\<gamma> = {s. \<sigma> s \<noteq> signal_of (def s) \<theta> s 0}"
          using `fst tw = 0`
          by (metis (no_types, lifting) Collect_cong One_nat_def \<open>derivative_hist_raw (snd tw)
          (get_time tw) = \<theta>\<close> des destruct_worldline_correctness(2) destruct_worldline_correctness(3)
          destruct_worldline_correctness(6) destruct_worldline_def diff_is_0_eq' le_add2 plus_1_eq_Suc
          worldline2_constructible)
        have "\<theta> = 0"
          unfolding `fst tw = 0` zero_fun_def
          by (metis \<open>get_time tw = 0\<close> \<open>derivative_hist_raw (snd tw) (get_time tw) = \<theta>\<close>
          derivative_hist_raw_def zero_option_def zero_order(1))
        hence "\<And>s. signal_of (def s) \<theta> s 0 = def s"
          using signal_of_empty by metis
        hence "\<gamma> = {s. \<sigma> s \<noteq> def s}"
          using \<gamma>_def' by auto
        moreover have "\<And>s.  snd (snd tw) s 0 = \<sigma> s"
          using `state_of_world (snd tw) (fst tw) = \<sigma>` `fst tw = 0` unfolding state_of_world_def by auto
        ultimately  have "\<gamma> = {s. snd (snd tw) s 0 \<noteq> def s}"
          by auto
        thus ?thesis  using ev by auto
      qed
    qed
    hence "beval_world_raw2 tw exp x"
      unfolding beval_world_raw2_def by auto
    have "beval_world_raw (snd tw) (fst tw) exp' x'"
    proof (intro beval_world_raw.intros)
      show " state_of_world (snd tw) (get_time tw) = \<sigma>"
        using des
        unfolding destruct_worldline_def Let_def state_of_world_def by auto
      show "derivative_hist_raw (snd tw) (fst tw) = \<theta>"
        using des
        unfolding destruct_worldline_def Let_def state_of_world_def by auto
      show "get_time tw , \<sigma> , \<gamma> , \<theta>, get_time (snd tw)  \<turnstile> exp' \<longrightarrow>\<^sub>b x' "
        by (metis (no_types, lifting) \<open>t , \<sigma> , \<gamma> , \<theta>, def \<turnstile> exp' \<longrightarrow>\<^sub>b x'\<close> des
        destruct_worldline_correctness(6) destruct_worldline_def fst_conv worldline2_constructible)
      show "event_of_world (snd tw) (fst tw) = \<gamma>"
      proof (cases "0 < fst tw")
        case True
        fix s
        have "snd (snd tw) s t = \<sigma> s"
          using `state_of_world (snd tw) (fst tw) = \<sigma>` unfolding state_of_world_def
          by (metis des fst_conv fst_destruct_worldline)
        moreover have "snd (snd tw) s (fst tw - 1) = signal_of (def s) \<theta> s (fst tw - 1)"
          unfolding worldline_raw_def using True
          by (metis (mono_tags, lifting) des \<open>derivative_hist_raw (snd tw) (get_time tw) = \<theta>\<close>
          destruct_worldline_correctness(6) destruct_worldline_def diff_less
          signal_of_derivative_hist_raw worldline2_constructible zero_less_one)
        ultimately show ?thesis
          unfolding event_of_world_def
          using True
          by (metis (mono_tags, lifting) des Collect_cong Pair_inject destruct_worldline_def
          diff_less less_numeral_extra(3) signal_of_derivative_hist_raw zero_less_one)
      next
        case False
        hence "fst tw = 0" by auto
        hence ev: "event_of_world (snd tw) (fst tw) = {s. snd (snd tw) s 0 \<noteq> def s}"
          unfolding event_of_world_def
          by (metis (mono_tags, lifting) des Collect_cong destruct_worldline_correctness(6)
          destruct_worldline_def worldline2_constructible)
        have \<gamma>_def': "\<gamma> = {s. \<sigma> s \<noteq> signal_of (def s) \<theta> s 0}"
          using `fst tw = 0`
          by (metis (no_types, lifting) Collect_cong One_nat_def \<open>derivative_hist_raw (snd tw)
          (get_time tw) = \<theta>\<close> des destruct_worldline_correctness(2) destruct_worldline_correctness(3)
          destruct_worldline_correctness(6) destruct_worldline_def diff_is_0_eq' le_add2 plus_1_eq_Suc
          worldline2_constructible)
        have "\<theta> = 0"
          unfolding `fst tw = 0` zero_fun_def
          by (metis \<open>get_time tw = 0\<close> \<open>derivative_hist_raw (snd tw) (get_time tw) = \<theta>\<close>
          derivative_hist_raw_def zero_option_def zero_order(1))
        hence "\<And>s. signal_of (def s) \<theta> s 0 = def s"
          using signal_of_empty by metis
        hence "\<gamma> = {s. \<sigma> s \<noteq> def s}"
          using \<gamma>_def' by auto
        moreover have "\<And>s.  snd (snd tw) s 0 = \<sigma> s"
          using `state_of_world (snd tw) (fst tw) = \<sigma>` `fst tw = 0` unfolding state_of_world_def by auto
        ultimately  have "\<gamma> = {s. snd (snd tw) s 0 \<noteq> def s}"
          by auto
        thus ?thesis  using ev by auto
      qed
    qed
    hence "beval_world_raw2 tw exp' x'"
      unfolding beval_world_raw2_def by auto
    have "x = x' \<or> x \<noteq> x'"
      by auto
    moreover
    { assume "x = x'"
      have "b_seq_exec t \<sigma> \<gamma> \<theta> def ss \<tau> \<tau>'"
        apply (rule seq_cases_bcase[OF exe, rotated])
        by (metis \<open>x = x'\<close> beval_raw_deterministic bevalx bevalx' choices.sel fst_conv list.sel(1)) blast+
      hence "tw, ss \<Rightarrow>\<^sub>s tw'"
        using des con by (auto intro!: world_seq_exec.intros)
      hence "Q tw'"
        using "*" \<open>beval_world_raw2 tw exp x\<close> \<open>beval_world_raw2 tw exp' x'\<close> \<open>x = x'\<close> by auto }
    moreover
    { assume "x \<noteq> x'"
      have "b_seq_exec t \<sigma> \<gamma> \<theta> def (Bcase exp choices) \<tau> \<tau>'"
        apply (rule seq_cases_bcase[OF exe])
        by (metis \<open>x \<noteq> x'\<close> beval_raw_deterministic bevalx bevalx' choices.sel fst_conv list.sel(1))
        blast+
      hence "tw, Bcase exp choices \<Rightarrow>\<^sub>s tw'"
        using des con by (auto intro!: world_seq_exec.intros)
      hence "Q tw'"
        using "*" \<open>beval_world_raw2 tw exp x\<close> \<open>beval_world_raw2 tw exp' x'\<close> \<open>x \<noteq> x'\<close> by auto }
    ultimately show "Q tw'"
      by auto
  qed
qed

lemma wp_trans:
  "0 < dly \<Longrightarrow> wp (Bassign_trans sig exp dly) Q = (\<lambda>tw. \<forall>x. beval_world_raw2 tw exp x \<longrightarrow> Q(tw [sig, dly :=\<^sub>2 x]))"
  apply (rule ext)
  unfolding wp_def
  by (metis lift_world_trans_worldline_upd2 world_seq_exec_trans)

lemma wp_inert:
  "0 < dly \<Longrightarrow> wp (Bassign_inert sig exp dly) Q = (\<lambda>tw. \<forall>x. beval_world_raw2 tw exp x \<longrightarrow> Q(tw \<lbrakk> sig, dly :=\<^sub>2 x \<rbrakk>))"
  apply (rule ext)
  unfolding wp_def
  by (metis lift_world_inert_worldline_upd2 world_seq_exec_inert)

lemma wp_is_pre: "nonneg_delay ss \<Longrightarrow> \<turnstile> [wp ss Q] ss [Q]"
proof (induction ss arbitrary: Q)
case (Bcomp ss1 ss2)
  then show ?case by (auto simp add: wp_bcomp)
next
  case (Bguarded g ss1 ss2)
  hence " \<turnstile> [wp ss1 Q] ss1 [Q]" and " \<turnstile> [wp ss2 Q] ss2 [Q]"
    using nonneg_delay.simps by blast+
  thus ?case
    apply (intro If2)
     apply (intro Conseq2[where Q'="Q" and s="ss1" and P="wp ss1 Q"])
    unfolding wp_guarded' apply simp
      apply assumption
     apply simp
    apply (intro Conseq2[where Q'="Q" and s="ss2" and P="wp ss2 Q"])
    unfolding wp_guarded apply simp
     apply assumption
    apply simp
    done
next
  case (Bassign_trans x1 x2 x3)
  then show ?case by (auto simp add: wp_trans)
next
  case (Bassign_inert x1 x2 x3)
  moreover have "0 < x3" using Bassign_inert by auto
  ultimately show ?case  using AssignI2 by (auto simp add: wp_inert)
next
  case Bnull
  then show ?case by (auto simp add: wp_bnull)
next
  case (Bcase exp choices)
  thus ?case
  proof (induct choices)
    case Nil
    then show ?case
      by (simp add: wp_bcase_empty)
  next
    case (Cons a choices)
    hence "nonneg_delay (Bcase exp choices)"
      unfolding nonneg_delay.simps by auto
    hence "\<turnstile> [wp (Bcase exp choices) Q] Bcase exp choices [Q]"
      using Cons by auto
    consider (others) ss' where "a = (Others, ss')" | (explicit) exp' ss' where "a = (Explicit exp', ss')"
      by (metis choices.collapse  old.prod.exhaust)
    then show ?case
    proof (cases)
      case others
      hence " \<turnstile> [wp ss' Q] ss' [Q]"
        using Cons.prems(1) Cons.prems(2) by fastforce
      then show ?thesis
        by (simp add: others wp_bcase_others)
    next
      case explicit
      hence "nonneg_delay (Bcase exp choices)"
        using \<open>nonneg_delay (Bcase exp choices)\<close> by blast
      hence " \<turnstile> [wp ss' Q] ss' [Q]"
        using Cons.prems(1) Cons.prems(2) explicit by fastforce
      show ?thesis
        unfolding explicit wp_bcase_explicit
        apply (rule Bcase_if2)
         apply (rule strengthen_pre_hoare2[where P="wp ss' Q"])
          apply auto[1]
         apply (rule \<open>\<turnstile> [wp ss' Q] ss' [Q]\<close>)
        apply (rule strengthen_pre_hoare2[where P=" wp (Bcase exp choices) Q"])
         apply auto[1]
        by (simp add: \<open>\<turnstile> [wp (Bcase exp choices) Q] Bcase exp choices [Q]\<close>)
    qed
  qed
qed

lemma hoare_complete:
  assumes "nonneg_delay ss" assumes "\<Turnstile> [P] ss [Q]" shows "\<turnstile> [P] ss [Q]"
proof (rule strengthen_pre_hoare2)
  show "\<forall>w. P w \<longrightarrow> wp ss Q w" using assms
    by (metis seq_hoare_valid2_def wp_def)
  show " \<turnstile> [VHDL_Hoare_Complete.wp ss Q] ss [Q]"
    using assms by (intro wp_is_pre)
qed

corollary hoare_sound_complete:
  assumes "nonneg_delay ss"
  shows "\<turnstile> [P] ss [Q] \<longleftrightarrow> \<Turnstile> [P] ss [Q]"
  using hoare_complete soundness_hoare2 assms by auto

subsection \<open>A sound and complete Hoare logic for VHDL's concurrent statement\<close>

definition event_of :: "nat \<times> 'signal worldline_init  \<Rightarrow> 'signal event" where
  "event_of tw = (fst o snd o snd) (destruct_worldline tw)"

lemma event_of_alt_def1:
  "0 < fst tw \<Longrightarrow> event_of tw = {s. wline_of tw s (fst tw) \<noteq> wline_of tw s (fst tw - 1)}"
proof-
  assume "0 < fst tw"
  obtain t \<sigma> \<gamma> \<theta> def \<tau> where des: "destruct_worldline tw = (t, \<sigma>, \<gamma>, \<theta>, def, \<tau>)"
    using prod_cases5 by metis
  hence "event_of tw = \<gamma>"
    unfolding event_of_def by auto
  also have "... = {s. \<sigma> s \<noteq> signal_of (def s) \<theta> s (t - 1)}"
    using \<open>destruct_worldline tw = (t, \<sigma>, \<gamma>, \<theta>, def, \<tau>)\<close> unfolding destruct_worldline_def Let_def
    by auto
  finally have "event_of tw = {s. \<sigma> s \<noteq> signal_of (def s) \<theta> s (t - 1)}"
    by auto
  have "\<And>s. \<sigma> s = wline_of tw s (fst tw)"
    using des unfolding destruct_worldline_def Let_def by auto
  have \<theta>_def: "\<theta> = derivative_hist_raw (snd tw) (get_time tw)" and t_def: "t = fst tw"
    using des unfolding destruct_worldline_def Let_def by auto
  have "\<And>s. signal_of (def s) \<theta> s (t - 1) = wline_of tw s (fst tw - 1)"
    using \<open>0 < fst tw\<close> unfolding \<theta>_def t_def
    by (metis (mono_tags, lifting) comp_apply des destruct_worldline_correctness(6)
        destruct_worldline_def diff_less signal_of_derivative_hist_raw worldline2_constructible
        zero_less_one)
  thus ?thesis
    using \<open>\<And>s. \<sigma> s = wline_of tw s (get_time tw)\<close> \<open>event_of tw = {s. \<sigma> s \<noteq> signal_of (def s) \<theta> s (t - 1)}\<close>
    by auto
qed

lemma event_of_alt_def2:
  "fst tw = 0 \<Longrightarrow> event_of tw = {s. wline_of tw s (fst tw) \<noteq> ((fst o snd) tw s)}"
proof -
  assume "fst tw = 0"
  obtain def t \<sigma> \<gamma> \<theta> \<tau> where des: "destruct_worldline tw = (t, \<sigma>, \<gamma>, \<theta>, def, \<tau>)"
    using prod_cases5 by metis
  hence "event_of tw = \<gamma>"
    unfolding event_of_def by auto
  also have "... = {s. \<sigma> s \<noteq> signal_of (def s) \<theta> s (t - 1)}"
    using \<open>destruct_worldline tw = (t, \<sigma>, \<gamma>, \<theta>, def, \<tau>)\<close> unfolding destruct_worldline_def Let_def
    by auto
  finally have "event_of tw = {s. \<sigma> s \<noteq> signal_of (def s) \<theta> s (t - 1)}"
    by auto
  have "\<And>s. \<sigma> s = wline_of tw s (fst tw)"
    using des unfolding destruct_worldline_def Let_def by auto
  have \<theta>_def: "\<theta> = derivative_hist_raw (snd tw) (get_time tw)" and t_def: "t = fst tw"
    using des unfolding destruct_worldline_def Let_def by auto
  have "\<And>s. signal_of (def s) \<theta> s (t - 1) = (def s)"
    using \<open>fst tw = 0\<close> unfolding \<theta>_def t_def
    by (metis derivative_hist_raw_def diff_0_eq_0 le_numeral_extra(3) signal_of_zero zero_option_def)
  thus ?thesis
    using \<open>\<And>s. \<sigma> s = wline_of tw s (get_time tw)\<close> \<open>event_of tw = {s. \<sigma> s \<noteq> signal_of (def s) \<theta> s (t - 1)}\<close>
    by (metis (mono_tags, lifting) Collect_cong comp_apply des destruct_worldline_correctness(6)
    destruct_worldline_def worldline2_constructible)
qed

lemma event_of_alt_def:
  "event_of tw = (if fst tw = 0 then {s. wline_of tw s (fst tw) \<noteq> ((fst o snd) tw s)} else
                                     {s. wline_of tw s (fst tw) \<noteq> wline_of tw s (fst tw - 1)})"
  using event_of_alt_def1 event_of_alt_def2
  by (metis (mono_tags, lifting) gr0I)

inductive
  conc_hoare :: "'signal assn2 \<Rightarrow> 'signal conc_stmt \<Rightarrow> 'signal assn2 \<Rightarrow> bool"
  ("\<turnstile> (\<lbrace>(1_)\<rbrace>/ (_)/ \<lbrace>(1_)\<rbrace>)" 50)
  where
Single:  "\<turnstile> [\<lambda>tw. P tw \<and> \<not> disjnt sl (event_of tw)] ss [Q] \<Longrightarrow> \<forall>tw. P tw \<and> disjnt sl (event_of tw) \<longrightarrow> Q tw
    \<Longrightarrow> \<turnstile> \<lbrace>P\<rbrace> process sl : ss \<lbrace>Q\<rbrace>"
| Parallel:  "\<turnstile> \<lbrace>P\<rbrace> cs\<^sub>1 \<lbrace>R\<rbrace> \<Longrightarrow> \<turnstile> \<lbrace>R\<rbrace> cs\<^sub>2 \<lbrace>Q\<rbrace> \<Longrightarrow> conc_stmt_wf (cs\<^sub>1 || cs\<^sub>2) \<Longrightarrow> \<turnstile> \<lbrace>P\<rbrace> cs\<^sub>1 || cs\<^sub>2 \<lbrace>Q\<rbrace>"
| Parallel2: "\<turnstile> \<lbrace>P\<rbrace> cs\<^sub>2 \<lbrace>R\<rbrace> \<Longrightarrow> \<turnstile> \<lbrace>R\<rbrace> cs\<^sub>1 \<lbrace>Q\<rbrace> \<Longrightarrow> conc_stmt_wf (cs\<^sub>1 || cs\<^sub>2) \<Longrightarrow> \<turnstile> \<lbrace>P\<rbrace> cs\<^sub>1 || cs\<^sub>2 \<lbrace>Q\<rbrace>"
| Conseq': "\<lbrakk>\<forall>w. P' w \<longrightarrow> P w; \<turnstile> \<lbrace>P\<rbrace> c \<lbrace>Q\<rbrace>; \<forall>w. Q w \<longrightarrow> Q' w\<rbrakk> \<Longrightarrow> \<turnstile> \<lbrace>P'\<rbrace> c \<lbrace>Q'\<rbrace>"
| Conj2: "\<turnstile> \<lbrace>P\<rbrace> s \<lbrace>Q1\<rbrace> \<Longrightarrow> \<turnstile> \<lbrace>P\<rbrace> s \<lbrace>Q2\<rbrace> \<Longrightarrow> \<turnstile> \<lbrace>P\<rbrace> s \<lbrace>\<lambda>tw. Q1 tw \<and> Q2 tw\<rbrace>"

lemma strengthen_pre_conc_hoare:
  assumes "\<forall>w. P' w \<longrightarrow> P w" and "\<turnstile> \<lbrace>P\<rbrace> s \<lbrace>Q\<rbrace>"
  shows "\<turnstile> \<lbrace>P'\<rbrace> s \<lbrace>Q\<rbrace>"
  using assms by (blast intro: Conseq')

lemma weaken_post_conc_hoare:
  assumes "\<forall>w. Q w \<longrightarrow> Q' w" and "\<turnstile> \<lbrace>P\<rbrace> s \<lbrace>Q\<rbrace>"
  shows   "\<turnstile> \<lbrace>P\<rbrace> s \<lbrace>Q'\<rbrace>"
  using assms by (blast intro: Conseq')

inductive world_conc_exec :: "nat \<times> 'signal worldline_init \<Rightarrow> 'signal conc_stmt \<Rightarrow> nat \<times> 'signal worldline_init \<Rightarrow> bool"
    ("(_ , _) \<Rightarrow>\<^sub>c _") where
  "     destruct_worldline tw = (t, \<sigma>, \<gamma>, \<theta>, def, \<tau>)
   \<Longrightarrow>  b_conc_exec t \<sigma> \<gamma> \<theta> def c \<tau> \<tau>'
   \<Longrightarrow>  worldline2  t \<sigma>   \<theta> def \<tau>' = tw'
   \<Longrightarrow>  world_conc_exec tw c tw'"

(* Diagram for lifting the concurrent execution to the worldline level
 *
 *         w, t                    \<Rightarrow>\<^sub>c          w', t
 *           \<down>                                  \<up>
 *   destruct_worldline                      worldline2 t \<sigma> \<theta> \<tau>'
 *           \<down>                                  \<up>
 *         t, \<sigma>, \<gamma>, \<theta> \<turnstile> <c, \<tau>>    \<longrightarrow>\<^sub>c          \<tau>'
 *
 *)

inductive_cases world_conc_exec_cases [elim!] : "world_conc_exec tw c tw'"

lemma world_conc_exec_deterministic:
  assumes "tw, c \<Rightarrow>\<^sub>c tw1"
  assumes "tw, c \<Rightarrow>\<^sub>c tw2"
  shows   "tw2 = tw1"
  using assms
proof (induction arbitrary: tw2 rule:world_conc_exec.induct)
  case (1 tw t \<sigma> \<gamma> \<theta> def \<tau> c \<tau>' tw')
  obtain \<tau>2 where " t , \<sigma> , \<gamma> , \<theta>, def  \<turnstile> <c , \<tau>> \<longrightarrow>\<^sub>c \<tau>2" and "worldline2 t \<sigma> \<theta> def \<tau>' = tw2"
    using world_conc_exec_cases[OF 1(4)] 1(1)
    by (smt "1.hyps"(2) Pair_inject b_conc_exec_deterministic)
  hence "\<tau>2 = \<tau>'"
    using b_conc_exec_deterministic 1(2) by blast
  thus ?case
    using "1.hyps"(3) \<open>worldline2 t \<sigma> \<theta> def \<tau>' = tw2\<close> by blast
qed

inductive world_conc_exec_alt :: "nat \<times> 'signal worldline_init \<Rightarrow> 'signal conc_stmt \<Rightarrow> nat \<times> 'signal worldline_init \<Rightarrow> bool"  where
  "disjnt sl (event_of tw) \<Longrightarrow> world_conc_exec_alt tw (process sl : ss) tw"

| "world_seq_exec_alt tw ss tw' \<Longrightarrow> \<not> disjnt sl (event_of tw) \<Longrightarrow> world_conc_exec_alt tw (process sl : ss) tw'"

| "world_conc_exec_alt tw cs1 tw' \<Longrightarrow> world_conc_exec_alt tw' cs2 tw'' \<Longrightarrow> world_conc_exec_alt tw (cs1 || cs2) tw''"

| "world_conc_exec_alt tw cs2 tw' \<Longrightarrow> world_conc_exec_alt tw' cs1 tw'' \<Longrightarrow> world_conc_exec_alt tw (cs1 || cs2) tw''"

inductive_cases world_conc_exec_alt_cases [elim!] : "world_conc_exec tw (process sl : ss) tw'"
                                                    "world_conc_exec tw (cs1 || cs2) tw'"

lemma world_conc_exec_imp_world_conc_exec_alt:
  assumes "world_conc_exec tw cs tw'"
  assumes "conc_stmt_wf cs" and "nonneg_delay_conc cs"
  shows   "world_conc_exec_alt tw cs tw'"
  using assms
proof (induction rule: world_conc_exec.induct)
  case (1 tw t \<sigma> \<gamma> \<theta> def \<tau> c \<tau>' tw')
  then show ?case
  proof (induction c arbitrary: \<tau> \<tau>' tw tw')
    case (Bpar c1 c2)
    hence "context_invariant t \<sigma> \<gamma> \<theta> def \<tau>"
      using worldline2_constructible  by blast
    then obtain \<tau>'' where "t , \<sigma> , \<gamma> , \<theta>, def  \<turnstile> <c1 , \<tau>> \<longrightarrow>\<^sub>c \<tau>'' "
      using Bpar by blast
    hence "t , \<sigma> , \<gamma> , \<theta>, def  \<turnstile> <c2 , \<tau>''> \<longrightarrow>\<^sub>c \<tau>'"
      using b_conc_exec_sequential by (metis Bpar.prems(2) Bpar.prems(4))
    obtain tw'' where "world_conc_exec_alt tw c1 tw''" and "tw'' = worldline2 t \<sigma> \<theta> def \<tau>''"
      using Bpar(1)[OF Bpar(3) `t , \<sigma> , \<gamma> , \<theta>, def  \<turnstile> <c1 , \<tau>> \<longrightarrow>\<^sub>c \<tau>''`] ` conc_stmt_wf (c1 || c2)`
      by (metis Bpar.prems(5) conc_stmt_wf_def distinct_append nonneg_delay_conc.simps(2)
      signals_from.simps(2))
    have "context_invariant t \<sigma> \<gamma> \<theta> def \<tau>''"
      using b_conc_exec_preserves_context_invariant[OF `t , \<sigma> , \<gamma> , \<theta>, def  \<turnstile> <c1 , \<tau>> \<longrightarrow>\<^sub>c \<tau>''` \<open>context_invariant t \<sigma> \<gamma> \<theta> def \<tau>\<close> ]
      `conc_stmt_wf (c1 || c2)` unfolding conc_stmt_wf_def
      using Bpar.prems(5) nonneg_delay_conc.simps(2) by blast
    moreover have "\<forall>s. non_stuttering (to_trans_raw_sig \<tau>) \<sigma> s"
      using Bpar.prems(1) destruct_worldline_ensure_non_stuttering by blast
    moreover hence "\<forall>s. non_stuttering (to_trans_raw_sig \<tau>'') \<sigma> s"
      by (metis (no_types, lifting) Bpar.prems(4) Bpar.prems(5) \<open>context_invariant t \<sigma> \<gamma> \<theta> def \<tau>\<close> \<open>t
      , \<sigma> , \<gamma> , \<theta>, def \<turnstile> <c1 , \<tau>> \<longrightarrow>\<^sub>c \<tau>''\<close> b_conc_exec_preserves_non_stuttering conc_stmt_wf_def
      context_invariant_def distinct_append nonneg_delay_conc.simps(2) signals_from.simps(2))
    moreover have " \<forall>s. non_stuttering (to_trans_raw_sig \<theta>) def s"
      using Bpar.prems(1) destruct_worldline_ensure_non_stuttering_hist_raw by blast
    ultimately have  des2: "destruct_worldline tw'' = (t, \<sigma>, \<gamma>, \<theta>, def, \<tau>'')"
      using destruct_worldline_correctness3  by (simp add: destruct_worldline_correctness3 \<open>tw'' = worldline2 t \<sigma> \<theta> def \<tau>''\<close>)
    hence "world_conc_exec_alt tw'' c2 tw'"
      using Bpar(2)[OF des2 `t , \<sigma> , \<gamma> , \<theta>, def  \<turnstile> <c2 , \<tau>''> \<longrightarrow>\<^sub>c \<tau>'` Bpar(5)]
      by (metis Bpar.prems(4) Bpar.prems(5) conc_stmt_wf_def distinct_append
      nonneg_delay_conc.simps(2) signals_from.simps(2))
    then show ?case
      using \<open>world_conc_exec_alt tw c1 tw''\<close> world_conc_exec_alt.intros(3) by blast
  next
    case (Bsingle x1 x2)
    then show ?case
      by (metis comp_apply conc_cases(1) event_of_def fst_conv nonneg_delay_conc.simps(1) snd_conv
      world_conc_exec_alt.intros(1) world_conc_exec_alt.intros(2) world_seq_exec.intros
      world_seq_exec_imp_world_seq_exec_alt worldline2_constructible)
  qed
qed

lemma world_conc_exec_alt_imp_world_conc_exec:
  assumes "world_conc_exec_alt tw cs tw'"
  assumes "conc_stmt_wf cs" and "nonneg_delay_conc cs"
  shows   "world_conc_exec tw cs tw'"
  using assms
proof (induction rule:world_conc_exec_alt.induct)
  case (1 sl tw ss)
  show ?case
    by (smt "1.hyps" b_conc_exec.intros(1) destruct_worldline_def event_of_def fst_conv o_apply
    snd_conv world_conc_exec.intros worldline2_constructible)
next
  case (2 tw ss tw' sl)
  hence "world_seq_exec tw ss tw'"
    using world_seq_exec_alt_def by (metis nonneg_delay_conc.simps(1))
  then obtain t \<sigma> \<gamma> \<theta> def \<tau> \<tau>' where "destruct_worldline tw = (t, \<sigma>, \<gamma>, \<theta>, def, \<tau>)"
      and "b_seq_exec t \<sigma> \<gamma> \<theta> def ss \<tau> \<tau>'" and " worldline2 t \<sigma> \<theta> def \<tau>' = tw'" and "(event_of tw) = \<gamma>"
    using world_seq_exec_cases by (smt comp_apply event_of_def fst_conv snd_conv)
  thus ?case
    using 2(2)
    by (auto intro!: world_conc_exec.intros b_conc_exec.intros)
next
  case (3 tw cs1 tw' cs2 tw'')
  hence "tw , cs1 \<Rightarrow>\<^sub>c tw'" and "tw', cs2 \<Rightarrow>\<^sub>c tw''"
    by (simp add: conc_stmt_wf_def)+
  then obtain t \<sigma> \<gamma> \<theta> def \<tau> \<tau>' where "destruct_worldline tw = (t, \<sigma>, \<gamma>, \<theta>, def, \<tau>)"
    and ex1: "t, \<sigma>, \<gamma>, \<theta>, def \<turnstile> <cs1, \<tau>> \<longrightarrow>\<^sub>c \<tau>'" and "worldline2 t \<sigma> \<theta> def \<tau>' = tw'" and
    "context_invariant t \<sigma> \<gamma> \<theta> def \<tau>" and "context_invariant t \<sigma> \<gamma> \<theta> def \<tau>'"
    using worldline2_constructible
    by (smt "3.prems"(2) b_conc_exec_preserves_context_invariant nonneg_delay_conc.simps(2)
    world_conc_exec_cases)
  have "\<forall>s. non_stuttering (to_trans_raw_sig \<tau>) \<sigma> s"
    using \<open>destruct_worldline tw = (t, \<sigma>, \<gamma>, \<theta>, def, \<tau>)\<close> destruct_worldline_ensure_non_stuttering by blast
  hence "\<forall>s. non_stuttering (to_trans_raw_sig \<tau>') \<sigma> s"
    using b_conc_exec_preserves_non_stuttering[OF ex1 ] 3(5-6)
    by (metis (full_types) \<open>destruct_worldline tw = (t, \<sigma>, \<gamma>, \<theta>, def, \<tau>)\<close> conc_stmt_wf_def
    destruct_worldline_trans_zero_upto_now distinct_append nonneg_delay_conc.simps(2)
    signals_from.simps(2))
  moreover have "\<forall>s. non_stuttering (to_trans_raw_sig \<theta>) def s"
    using \<open>destruct_worldline tw = (t, \<sigma>, \<gamma>, \<theta>, def, \<tau>)\<close>
    destruct_worldline_ensure_non_stuttering_hist_raw by blast
  hence "destruct_worldline tw' = (t, \<sigma>, \<gamma>, \<theta>, def, \<tau>')"
    using \<open>context_invariant t \<sigma> \<gamma> \<theta> def \<tau>'\<close> \<open>worldline2 t \<sigma> \<theta> def \<tau>' = tw'\<close> calculation
    destruct_worldline_correctness3 by blast
  then obtain \<tau>'' where "t, \<sigma>, \<gamma>, \<theta>, def \<turnstile> <cs2, \<tau>'> \<longrightarrow>\<^sub>c \<tau>''" and "worldline2 t \<sigma> \<theta> def \<tau>'' = tw''"
    using \<open>tw' , cs2 \<Rightarrow>\<^sub>c tw''\<close> by auto
  obtain temp where "t, \<sigma>, \<gamma>, \<theta>, def \<turnstile> <cs1 || cs2, \<tau>> \<longrightarrow>\<^sub>c temp"
    by (meson \<open>t , \<sigma> , \<gamma> , \<theta>, def \<turnstile> <cs2 , \<tau>'> \<longrightarrow>\<^sub>c \<tau>''\<close> b_conc_exec.intros(3) ex1
    only_context_matters_for_progress_conc)
  hence "t, \<sigma>, \<gamma>, \<theta>, def \<turnstile> <cs1 || cs2, \<tau>>\<longrightarrow>\<^sub>c \<tau>''"
    using b_conc_exec_sequential'[OF 3(5) _ `t, \<sigma>, \<gamma>, \<theta>, def \<turnstile> <cs1, \<tau>> \<longrightarrow>\<^sub>c \<tau>'` `t, \<sigma>, \<gamma>, \<theta>, def \<turnstile> <cs2, \<tau>'> \<longrightarrow>\<^sub>c \<tau>''`]
    by auto
  then show ?case
    by (metis \<open>destruct_worldline tw = (t, \<sigma>, \<gamma>, \<theta>, def, \<tau>)\<close> \<open>worldline2 t \<sigma> \<theta> def \<tau>'' = tw''\<close>
    world_conc_exec.intros)
next
  case (4 tw cs2 tw' cs1 tw'')
  hence "tw , cs2 \<Rightarrow>\<^sub>c tw'" and "tw', cs1 \<Rightarrow>\<^sub>c tw''"
    by (simp add: conc_stmt_wf_def)+
  have "conc_stmt_wf (cs2 || cs1)"
    using 4(5) by (metis conc_stmt_wf_def disjoint_iff_not_equal distinct_append signals_from.simps(2))
  then obtain t \<sigma> \<gamma> \<theta> def \<tau> \<tau>' where "destruct_worldline tw = (t, \<sigma>, \<gamma>, \<theta>, def, \<tau>)"
    and ex1: "t, \<sigma>, \<gamma>, \<theta>, def \<turnstile> <cs2, \<tau>> \<longrightarrow>\<^sub>c \<tau>'" and "worldline2 t \<sigma> \<theta> def \<tau>' = tw'" and
    "context_invariant t \<sigma> \<gamma> \<theta> def \<tau>" and "context_invariant t \<sigma> \<gamma> \<theta> def \<tau>'"
    using worldline2_constructible `tw , cs2 \<Rightarrow>\<^sub>c tw'` `tw', cs1 \<Rightarrow>\<^sub>c tw''`
    by (smt "4.prems"(2) b_conc_exec_preserves_context_invariant nonneg_delay_conc.simps(2)
    world_conc_exec_cases)
  have "\<forall>s. non_stuttering (to_trans_raw_sig \<tau>) \<sigma> s"
    using \<open>destruct_worldline tw = (t, \<sigma>, \<gamma>, \<theta>, def, \<tau>)\<close> destruct_worldline_ensure_non_stuttering by blast
  hence "\<forall>s. non_stuttering (to_trans_raw_sig \<tau>') \<sigma> s"
    using b_conc_exec_preserves_non_stuttering[OF ex1 ] 4(5-6)
    by (metis (full_types) \<open>destruct_worldline tw = (t, \<sigma>, \<gamma>, \<theta>, def, \<tau>)\<close> conc_stmt_wf_def
    destruct_worldline_trans_zero_upto_now distinct_append nonneg_delay_conc.simps(2)
    signals_from.simps(2))
  moreover have "\<forall>s. non_stuttering (to_trans_raw_sig \<theta>) def s"
    using \<open>destruct_worldline tw = (t, \<sigma>, \<gamma>, \<theta>, def, \<tau>)\<close>
    destruct_worldline_ensure_non_stuttering_hist_raw by blast
  hence "destruct_worldline tw' = (t, \<sigma>, \<gamma>, \<theta>, def, \<tau>')"
    using \<open>context_invariant t \<sigma> \<gamma> \<theta> def \<tau>'\<close> \<open>worldline2 t \<sigma> \<theta> def \<tau>' = tw'\<close> calculation
    destruct_worldline_correctness3 by blast
  then obtain \<tau>'' where ex2: "t, \<sigma>, \<gamma>, \<theta>, def \<turnstile> <cs1, \<tau>'> \<longrightarrow>\<^sub>c \<tau>''" and "worldline2 t \<sigma> \<theta> def \<tau>'' = tw''"
    using \<open>tw' , cs1 \<Rightarrow>\<^sub>c tw''\<close> by auto
  obtain temp where "t, \<sigma>, \<gamma>, \<theta>, def \<turnstile> <cs1 || cs2, \<tau>> \<longrightarrow>\<^sub>c temp"
    by (meson \<open>t , \<sigma> , \<gamma> , \<theta>, def \<turnstile> <cs1 , \<tau>'> \<longrightarrow>\<^sub>c \<tau>''\<close> b_conc_exec.intros(3) ex1
    only_context_matters_for_progress_conc)
  hence "t, \<sigma>, \<gamma>, \<theta>, def \<turnstile> <cs1 || cs2, \<tau>>\<longrightarrow>\<^sub>c \<tau>''"
    using b_conc_exec_sequential'[OF `conc_stmt_wf (cs2 || cs1)` _ ex1 ex2]
    by (metis "4.prems"(1) parallel_comp_commute)
  then show ?case
    by (metis \<open>destruct_worldline tw = (t, \<sigma>, \<gamma>, \<theta>, def, \<tau>)\<close> \<open>worldline2 t \<sigma> \<theta> def \<tau>'' = tw''\<close>
    world_conc_exec.intros)
qed

lemma world_conc_exec_eq_world_conc_exec_alt:
  assumes "conc_stmt_wf cs" and "nonneg_delay_conc cs"
  shows   "world_conc_exec_alt tw cs = world_conc_exec tw cs"
  by (rule, rule)
     (auto simp add: world_conc_exec_alt_imp_world_conc_exec world_conc_exec_imp_world_conc_exec_alt assms)

lemma fst_world_conc_exec:
  assumes "tw, cs \<Rightarrow>\<^sub>c tw'"
  shows "fst tw = fst tw'"
proof -
  have "world_conc_exec tw cs tw'"
    using assms by auto
  obtain t \<sigma> \<gamma> \<theta> def \<tau> where "destruct_worldline tw = (t, \<sigma>, \<gamma>, \<theta>, def, \<tau>)"
    using destruct_worldline_exist by blast
  then obtain \<tau>' where "b_conc_exec t \<sigma> \<gamma> \<theta> def cs \<tau> \<tau>'"
    using world_conc_exec_cases[OF assms] by fastforce
  have "fst tw = t"
    using fst_destruct_worldline `destruct_worldline tw = (t, \<sigma>, \<gamma>, \<theta>, def, \<tau>)`  by (metis fst_conv)
  have "fst tw' = fst (worldline2 t \<sigma> \<theta> def \<tau>')"
    using `world_conc_exec tw cs tw'` `destruct_worldline tw = (t, \<sigma>, \<gamma>, \<theta>, def, \<tau>)`
    by auto
  also have "... = t"
    by transfer' auto
  also have "... = fst tw"
    using `fst tw = t` by auto
  finally show "fst tw = fst tw'"
    by auto
qed

lemma world_conc_exec_commute:
  assumes "tw, (cs1 || cs2) \<Rightarrow>\<^sub>c tw1"
  assumes "tw, (cs2 || cs1) \<Rightarrow>\<^sub>c tw2"
  assumes "conc_stmt_wf (cs1 || cs2)"
  shows "tw1 = tw2"
proof -
  obtain t \<sigma> \<gamma> \<theta> def \<tau> \<tau>' where "destruct_worldline tw = (t, \<sigma>, \<gamma>, \<theta>, def, \<tau>)" and
    "t, \<sigma>, \<gamma>, \<theta>, def \<turnstile> <cs1 || cs2, \<tau>> \<longrightarrow>\<^sub>c \<tau>'" and "worldline2 t \<sigma> \<theta> def \<tau>' = tw1"
    using assms(1)  by (smt world_conc_exec_cases)
  hence "t, \<sigma>, \<gamma>, \<theta>, def \<turnstile> <cs2 || cs1, \<tau>> \<longrightarrow>\<^sub>c \<tau>'"
    using parallel_comp_commute'[OF assms(3)] by auto
  thus ?thesis
    using assms(2) \<open>destruct_worldline tw = (t, \<sigma>, \<gamma>, \<theta>, def, \<tau>)\<close> \<open>worldline2 t \<sigma> \<theta> def \<tau>' = tw1\<close>
    by (smt b_conc_exec_deterministic fst_conv snd_conv world_conc_exec_cases)
qed

lemma world_conc_exec_disjnt:
  fixes tw :: "nat \<times> 'a worldline_init"
  assumes "disjnt sl (event_of tw)" shows "tw, (process sl : ss) \<Rightarrow>\<^sub>c tw"
proof -
  obtain t \<sigma> \<gamma> \<theta> \<tau> def \<tau>' where des: "destruct_worldline tw = (t, \<sigma>, \<gamma>, \<theta>, def , \<tau>)" and
    ex: "t, \<sigma>, \<gamma>, \<theta>, def \<turnstile> <process sl : ss, \<tau>> \<longrightarrow>\<^sub>c \<tau>'"
    using destruct_worldline_exist
    by (smt assms b_conc_exec.intros(1) comp_apply event_of_def fst_conv snd_conv)
  moreover have "disjnt sl \<gamma>"
    using assms unfolding event_of_def by (simp add: des)
  ultimately have "\<tau>' = \<tau>"
    by auto
  hence "worldline2 t \<sigma> \<theta> def \<tau>' = tw"
    using des  worldline2_constructible by fastforce
  with des ex show ?thesis
    by (meson world_conc_exec.intros)
qed

lemma world_conc_exec_not_disjnt:
  fixes tw :: "nat \<times> 'a worldline_init"
  assumes "\<not> disjnt sl (event_of tw)" and "tw, ss \<Rightarrow>\<^sub>s tw'"
  shows "tw, (process sl : ss) \<Rightarrow>\<^sub>c tw'"
proof -
  obtain t \<sigma> \<gamma> \<theta> \<tau> def \<tau>' where des: "destruct_worldline tw = (t, \<sigma>, \<gamma>, \<theta>, def, \<tau>)" and
    ex: "t, \<sigma>, \<gamma>, \<theta>, def \<turnstile> <process sl : ss, \<tau>> \<longrightarrow>\<^sub>c \<tau>'"
    using destruct_worldline_exist
    by (smt assms(2) b_conc_exec.intros(1) b_conc_exec.intros(2) world_seq_exec_cases)
  moreover have "\<not> disjnt sl \<gamma>"
    using assms unfolding event_of_def des by (simp add: des)
  ultimately have "b_seq_exec t \<sigma> \<gamma> \<theta> def ss \<tau> \<tau>'"
    by auto
  hence "worldline2 t \<sigma> \<theta> def \<tau>' = tw'"
    using assms(2) des  by (smt b_seq_exec_deterministic fst_conv snd_conv world_seq_exec_cases)
  thus ?thesis
    using des ex
    by (meson world_conc_exec.intros) qed

definition
conc_hoare_valid :: "'signal assn2 \<Rightarrow> 'signal conc_stmt \<Rightarrow> 'signal assn2 \<Rightarrow> bool" ("\<Turnstile> \<lbrace>(1_)\<rbrace>/ (_)/ \<lbrace>(1_)\<rbrace>" 50)
where "\<Turnstile> \<lbrace>P\<rbrace> c \<lbrace>Q\<rbrace> \<longleftrightarrow>  (\<forall>tw tw'.  P tw \<and> (tw, c \<Rightarrow>\<^sub>c tw') \<longrightarrow> Q tw')"

lemma helper_b_conc:
  assumes "t, \<sigma>, \<gamma>, \<theta>1, def \<turnstile> <cs, \<tau>1> \<longrightarrow>\<^sub>c \<tau>1'"
  assumes "\<And>k s. signal_of (def s) \<theta>1 s k = signal_of (def s) \<theta>2 s k"
  assumes "\<And>k s. signal_of (\<sigma> s) \<tau>1 s k = signal_of (\<sigma> s) \<tau>2 s k"
  assumes "t, \<sigma>, \<gamma>, \<theta>2, def \<turnstile> <cs, \<tau>2> \<longrightarrow>\<^sub>c \<tau>2'"
  assumes "\<forall>n. n \<le> t \<longrightarrow>  \<tau>1 n = 0"
  assumes "\<forall>n. n \<le> t \<longrightarrow>  \<tau>2 n = 0"
  assumes "\<forall>n. t \<le> n \<longrightarrow>  \<theta>1 n = 0"
  assumes "\<forall>n. t \<le> n \<longrightarrow>  \<theta>2 n = 0"
  assumes "nonneg_delay_conc cs"
  assumes "\<forall>s. non_stuttering (to_trans_raw_sig \<tau>1) \<sigma> s"
  assumes "\<forall>s. non_stuttering (to_trans_raw_sig \<tau>2) \<sigma> s"
  shows "\<And>k s. signal_of (\<sigma> s) \<tau>1' s k = signal_of (\<sigma> s) \<tau>2' s k"
  using assms
proof (induction cs arbitrary: \<tau>1 \<tau>2 \<tau>1' \<tau>2')
  case (Bpar cs1 cs2)
  then obtain \<tau>11 \<tau>12 where "b_conc_exec t \<sigma> \<gamma> \<theta>1 def cs1 \<tau>1 \<tau>11" and "b_conc_exec t \<sigma> \<gamma> \<theta>1 def cs2 \<tau>1 \<tau>12"
    by blast
  hence \<tau>1'_def: "\<tau>1' = clean_zip_raw \<tau>1 (\<tau>11, set (signals_from cs1)) (\<tau>12, set (signals_from cs2))"
    using Bpar by (smt obtain_clean_zip)
  then obtain \<tau>21 and \<tau>22 where "b_conc_exec t \<sigma> \<gamma> \<theta>2 def cs1 \<tau>2 \<tau>21" and  "b_conc_exec t \<sigma> \<gamma> \<theta>2 def cs2 \<tau>2 \<tau>22"
    using Bpar.prems(4) by blast
  hence \<tau>2'_def: "\<tau>2' = clean_zip_raw \<tau>2 (\<tau>21, set (signals_from cs1)) (\<tau>22, set (signals_from cs2))"
    using  Bpar  by (smt obtain_clean_zip)
  hence ind1: "\<And>s k. signal_of (\<sigma> s) \<tau>11 s k = signal_of (\<sigma> s) \<tau>21 s k"
    using Bpar(1)[OF _ Bpar(4-5) _ Bpar(7-10), of "\<tau>11" "\<tau>21"]  Bpar.prems(9) nonneg_delay_conc.simps(2)
    Bpar.prems(10) Bpar.prems(11) \<open>t , \<sigma> , \<gamma> , \<theta>1, def \<turnstile> <cs1 , \<tau>1> \<longrightarrow>\<^sub>c \<tau>11\<close> \<open>t , \<sigma> , \<gamma> , \<theta>2, def \<turnstile> <cs1 , \<tau>2> \<longrightarrow>\<^sub>c \<tau>21\<close> by blast
  hence ind2: "\<And>s k. signal_of (\<sigma> s) \<tau>12 s k = signal_of (\<sigma> s) \<tau>22 s k"
    using Bpar(2)[OF _ Bpar(4-5) _ Bpar(7-10), of "\<tau>12" "\<tau>22"]  Bpar.prems(9)
    by (simp add: Bpar.prems(10) Bpar.prems(11) \<open>t , \<sigma> , \<gamma> , \<theta>1, def \<turnstile> <cs2 , \<tau>1> \<longrightarrow>\<^sub>c \<tau>12\<close> \<open>t , \<sigma> ,
    \<gamma> , \<theta>2, def \<turnstile> <cs2 , \<tau>2> \<longrightarrow>\<^sub>c \<tau>22\<close>)
  have "s \<in> set (signals_from cs1) \<or> s \<notin> set (signals_from cs1) \<and> s \<in> set (signals_from cs2) \<or>
        s \<notin> set (signals_from cs1) \<and> s \<notin> set (signals_from cs2)"
    by auto
  moreover
  { assume "s \<in> set (signals_from cs1)"
    hence "\<And>n. (to_trans_raw_sig \<tau>1' s) =  (to_trans_raw_sig \<tau>11 s)"
      using \<tau>1'_def unfolding to_trans_raw_sig_def clean_zip_raw_def Let_def by (auto split:prod.splits)
    moreover have "\<And>n.  (to_trans_raw_sig \<tau>2' s) =  (to_trans_raw_sig \<tau>21 s)"
      using `s \<in> set (signals_from cs1)` \<tau>2'_def
      unfolding to_trans_raw_sig_def clean_zip_raw_def Let_def by (auto split:prod.splits)
    ultimately have  ?case
      using  ind1 ind2 by (metis signal_of_equal_when_trans_sig_equal_upto to_trans_raw_sig_def) }
  moreover
  { assume *: "s \<notin> set (signals_from cs1) \<and> s \<in> set (signals_from cs2)"
    hence "\<And>n.  (to_trans_raw_sig \<tau>1' s) =  (to_trans_raw_sig \<tau>12 s)"
      using \<tau>1'_def
      unfolding to_trans_raw_sig_def clean_zip_raw_def Let_def by (auto split:prod.splits)
    moreover have "\<And>n.  (to_trans_raw_sig \<tau>2' s) =  (to_trans_raw_sig \<tau>22 s)"
      using * \<tau>2'_def
      unfolding to_trans_raw_sig_def clean_zip_raw_def Let_def by (auto split:prod.splits)
    ultimately have  ?case
      using  ind1 ind2
      by (metis signal_of_equal_when_trans_sig_equal_upto to_trans_raw_sig_def) }
  moreover
  { assume *: "s \<notin> set (signals_from cs1) \<and> s \<notin> set (signals_from cs2)"
    hence "\<And>n.  (to_trans_raw_sig \<tau>1' s) =  (to_trans_raw_sig \<tau>1 s)"
      using \<tau>1'_def
      unfolding to_trans_raw_sig_def clean_zip_raw_def Let_def by (auto split:prod.splits)
    moreover have "\<And>n.  (to_trans_raw_sig \<tau>2' s) =  (to_trans_raw_sig \<tau>2 s)"
      using * \<tau>2'_def
      unfolding to_trans_raw_sig_def clean_zip_raw_def Let_def by (auto split:prod.splits)
    ultimately have  ?case
      using ind1 ind2 Bpar(5)
      by (metis signal_of_equal_when_trans_sig_equal_upto to_trans_raw_sig_def) }
  ultimately show ?case by auto
next
  case (Bsingle sl ss)
  have "disjnt sl \<gamma> \<or> \<not> disjnt sl \<gamma>"
    by auto
  moreover
  { assume "disjnt sl \<gamma>"
    hence "\<tau>1' = \<tau>1" and "\<tau>2' = \<tau>2"
      using Bsingle by auto
    with Bsingle(3) have ?case by auto }
  moreover
  { assume "\<not> disjnt sl \<gamma>"
    hence tau1': "t, \<sigma>, \<gamma>, \<theta>1, def \<turnstile> < ss, \<tau>1> \<longrightarrow>\<^sub>s \<tau>1'" and tau2': "t, \<sigma>, \<gamma>, \<theta>2, def \<turnstile> < ss, \<tau>2> \<longrightarrow>\<^sub>s \<tau>2'"
      using Bsingle by auto
    have "nonneg_delay ss"
      using Bsingle by auto
    hence ?case
      using helper'[OF tau1' Bsingle(2-3) tau2' Bsingle(5-8)] Bsingle.prems(10) Bsingle.prems(11)
      by blast }
  ultimately show ?case by auto
qed

lemma helper_init':
  assumes "init' t \<sigma> \<gamma> \<theta>1 def cs \<tau>1 \<tau>1'"
  assumes "\<And>k s. signal_of (def s) \<theta>1 s k = signal_of (def s) \<theta>2 s k"
  assumes "\<And>k s. signal_of (\<sigma> s) \<tau>1 s k = signal_of (\<sigma> s) \<tau>2 s k"
  assumes "init' t \<sigma> \<gamma> \<theta>2 def cs \<tau>2 \<tau>2'"
  assumes "\<forall>n. n \<le> t \<longrightarrow>  \<tau>1 n = 0"
  assumes "\<forall>n. n \<le> t \<longrightarrow>  \<tau>2 n = 0"
  assumes "\<forall>n. t \<le> n \<longrightarrow>  \<theta>1 n = 0"
  assumes "\<forall>n. t \<le> n \<longrightarrow>  \<theta>2 n = 0"
  assumes "nonneg_delay_conc cs"
  assumes "\<forall>s. non_stuttering (to_trans_raw_sig \<tau>1) \<sigma> s"
  assumes "\<forall>s. non_stuttering (to_trans_raw_sig \<tau>2) \<sigma> s"
  shows "\<And>k s. signal_of (\<sigma> s) \<tau>1' s k = signal_of (\<sigma> s) \<tau>2' s k"
  using assms
proof (induction cs arbitrary: \<tau>1 \<tau>2 \<tau>1' \<tau>2')
  case (Bpar cs1 cs2)
  then obtain \<tau>11 \<tau>12 where \<tau>11_def : "init' t \<sigma> \<gamma> \<theta>1 def cs1 \<tau>1 \<tau>11" and \<tau>12_def: "init' t \<sigma> \<gamma> \<theta>1 def cs2 \<tau>1 \<tau>12"
    by blast
  hence \<tau>1'_def: "\<tau>1' = clean_zip_raw \<tau>1 (\<tau>11, set (signals_from cs1)) (\<tau>12, set (signals_from cs2))"
    using \<tau>11_def Bpar by (meson init'.intros(2) init'_deterministic)
  then obtain \<tau>21 \<tau>22 where \<tau>21_def: "init' t \<sigma> \<gamma> \<theta>2 def cs1 \<tau>2 \<tau>21" and \<tau>22_def: "init' t \<sigma> \<gamma> \<theta>2 def cs2 \<tau>2 \<tau>22"
    using Bpar.prems(4) by blast
  hence \<tau>2'_def: "\<tau>2' = clean_zip_raw \<tau>2 (\<tau>21, set (signals_from cs1)) (\<tau>22, set (signals_from cs2))"
    using \<tau>21_def Bpar  by (metis init'.intros(2) init'_deterministic)
  hence ind1: "\<And>s k. signal_of (\<sigma> s) \<tau>11 s k = signal_of (\<sigma> s) \<tau>21 s k"
    using Bpar(1)[OF _ Bpar(4-5) _ Bpar(7-10), of "\<tau>11" "\<tau>21"] \<tau>11_def \<tau>21_def
    using Bpar.prems(9) nonneg_delay_conc.simps(2)
    by (simp add: Bpar.prems(10) Bpar.prems(11))
  hence ind2: "\<And>s k. signal_of (\<sigma> s) \<tau>12 s k = signal_of (\<sigma> s) \<tau>22 s k"
    using Bpar(2)[OF _ Bpar(4-5) _ Bpar(7-10), of "\<tau>12" "\<tau>22"] \<tau>12_def \<tau>22_def
    using Bpar.prems(9)  by (simp add: Bpar.prems(10) Bpar.prems(11))
  have "s \<in> set (signals_from cs1) \<or> s \<notin> set (signals_from cs1) \<and> s \<in> set (signals_from cs2) \<or>
        s \<notin> set (signals_from cs1) \<and> s \<notin> set (signals_from cs2)"
    by auto
  moreover
  { assume "s \<in> set (signals_from cs1)"
    hence "\<And>n. (to_trans_raw_sig \<tau>1' s) =  (to_trans_raw_sig \<tau>11 s)"
      using \<tau>1'_def unfolding to_trans_raw_sig_def clean_zip_raw_def Let_def by (auto split:prod.splits)
    moreover have "\<And>n.  (to_trans_raw_sig \<tau>2' s) =  (to_trans_raw_sig \<tau>21 s)"
      using `s \<in> set (signals_from cs1)` \<tau>2'_def
      unfolding to_trans_raw_sig_def clean_zip_raw_def Let_def by (auto split:prod.splits)
    ultimately have  ?case
      using  ind1 ind2 by (metis signal_of_equal_when_trans_sig_equal_upto to_trans_raw_sig_def) }
  moreover
  { assume *: "s \<notin> set (signals_from cs1) \<and> s \<in> set (signals_from cs2)"
    hence "\<And>n.  (to_trans_raw_sig \<tau>1' s) =  (to_trans_raw_sig \<tau>12 s)"
      using \<tau>1'_def
      unfolding to_trans_raw_sig_def clean_zip_raw_def Let_def by (auto split:prod.splits)
    moreover have "\<And>n.  (to_trans_raw_sig \<tau>2' s) =  (to_trans_raw_sig \<tau>22 s)"
      using * \<tau>2'_def
      unfolding to_trans_raw_sig_def clean_zip_raw_def Let_def by (auto split:prod.splits)
    ultimately have  ?case
      using  ind1 ind2
      by (metis signal_of_equal_when_trans_sig_equal_upto to_trans_raw_sig_def) }
  moreover
  { assume *: "s \<notin> set (signals_from cs1) \<and> s \<notin> set (signals_from cs2)"
    hence "\<And>n.  (to_trans_raw_sig \<tau>1' s) =  (to_trans_raw_sig \<tau>1 s)"
      using \<tau>1'_def
      unfolding to_trans_raw_sig_def clean_zip_raw_def Let_def by (auto split:prod.splits)
    moreover have "\<And>n.  (to_trans_raw_sig \<tau>2' s) =  (to_trans_raw_sig \<tau>2 s)"
      using * \<tau>2'_def
      unfolding to_trans_raw_sig_def clean_zip_raw_def Let_def by (auto split:prod.splits)
    ultimately have  ?case
      using ind1 ind2 Bpar(5)
      by (metis signal_of_equal_when_trans_sig_equal_upto to_trans_raw_sig_def) }
  ultimately show ?case by auto
next
  case (Bsingle sl ss)
  hence tau1': "t, \<sigma>, \<gamma>, \<theta>1, def \<turnstile> < ss, \<tau>1> \<longrightarrow>\<^sub>s \<tau>1'" and tau2': "t, \<sigma>, \<gamma>, \<theta>2, def \<turnstile> < ss, \<tau>2> \<longrightarrow>\<^sub>s \<tau>2'"
    using Bsingle by auto
  have "nonneg_delay ss"
    using Bsingle by auto
  thus ?case
    using helper'[OF tau1' Bsingle(2-3) tau2' Bsingle(5-8)]
    by (simp add: Bsingle.prems(10) Bsingle.prems(11))
qed

lemma world_conc_exec_parallel:
  assumes "conc_stmt_wf (cs1 || cs2)" and "nonneg_delay_conc (cs1 || cs2)"
  assumes "world_conc_exec tw   cs1 tw''"
  assumes "world_conc_exec tw'' cs2 tw' "
  assumes "tw, (cs1 || cs2) \<Rightarrow>\<^sub>c tw_res"
  shows "tw_res = tw'"
proof -
  have "nonneg_delay_conc cs1" and "nonneg_delay_conc cs2"
    using assms by auto
  obtain t \<sigma> \<gamma> \<theta> \<tau> def \<tau>' where des: "destruct_worldline tw = (t, \<sigma>, \<gamma>, \<theta>, def, \<tau>)" and
    ex: "t, \<sigma>, \<gamma>, \<theta>, def \<turnstile> <cs1, \<tau>> \<longrightarrow>\<^sub>c \<tau>'" and ci: "context_invariant t \<sigma> \<gamma> \<theta> def \<tau>"
    using destruct_worldline_exist worldline2_constructible assms(3) by blast
  have "\<forall>s. non_stuttering (to_trans_raw_sig \<tau>) \<sigma> s"
    using destruct_worldline_ensure_non_stuttering[OF des] by auto
  have "\<And>n. n \<le> t \<Longrightarrow> \<tau> n = 0"
    using destruct_worldline_trans_zero_upto_now[OF des] by auto
  have "\<forall>s. non_stuttering (to_trans_raw_sig \<tau>') \<sigma> s"
  proof (rule)
    fix s
    have "non_stuttering (to_trans_raw_sig \<tau>) \<sigma> s"
      using `\<forall>s. non_stuttering (to_trans_raw_sig \<tau>) \<sigma> s` by auto
    moreover have "conc_stmt_wf cs1" and "nonneg_delay_conc cs1"
      using assms by auto
    thus "non_stuttering (to_trans_raw_sig \<tau>') \<sigma> s"
      using b_conc_exec_preserves_non_stuttering[OF ex `non_stuttering (to_trans_raw_sig \<tau>) \<sigma> s`
      `\<And>n. n \<le> t \<Longrightarrow> \<tau> n = 0`] by auto
  qed
  have ci': "context_invariant t \<sigma> \<gamma> \<theta> def \<tau>'"
    using b_conc_exec_preserves_context_invariant[OF ex ci `nonneg_delay_conc cs1`] by auto
  hence wcs1: "world_conc_exec tw cs1 (worldline2 t \<sigma> \<theta> def \<tau>')"
    using des ex world_conc_exec.intros by blast
  have "\<forall>s. non_stuttering (to_trans_raw_sig \<theta>) def s"
    using des destruct_worldline_ensure_non_stuttering_hist_raw by blast
  hence "destruct_worldline (worldline2 t \<sigma> \<theta> def \<tau>') = (t, \<sigma>, \<gamma>, \<theta>, def, \<tau>')"
    using destruct_worldline_correctness3[OF ci' `\<forall>s. non_stuttering (to_trans_raw_sig \<tau>') \<sigma> s`]
    by blast
  obtain theta tau' where des2: "destruct_worldline (worldline2 t \<sigma> \<theta> def \<tau>') = (t, \<sigma>, \<gamma>, theta, def, tau')"
    and beh_same: "\<And>k s. signal_of (def s) \<theta> s k = signal_of (def s) theta s k" and
        trans_same: "\<And>k s. signal_of (\<sigma> s) \<tau>' s k = signal_of (\<sigma> s) tau' s k"
    using destruct_worldline_correctness[OF ci'] by (metis prod_cases4)
  obtain \<tau>'' where "t, \<sigma>, \<gamma>, \<theta>, def \<turnstile> <cs2, \<tau>'> \<longrightarrow>\<^sub>c \<tau>''"
    using \<open>destruct_worldline (worldline2 t \<sigma> \<theta> def \<tau>') = (t, \<sigma>, \<gamma>, \<theta>, def, \<tau>')\<close> assms(3) assms(4) b_conc_exec_deterministic wcs1 by fastforce
  have "\<exists>\<tau>'. t , \<sigma> , \<gamma> , \<theta>, def  \<turnstile> <cs1 || cs2 , \<tau>> \<longrightarrow>\<^sub>c \<tau>'"
    by (smt assms(5) des old.prod.inject world_conc_exec_cases)
  hence "b_conc_exec t \<sigma> \<gamma> \<theta> def (cs1 || cs2) \<tau> \<tau>''"
    using b_conc_exec_sequential'[OF assms(1) _ ex \<open>t, \<sigma>, \<gamma>, \<theta>, def \<turnstile> <cs2, \<tau>'> \<longrightarrow>\<^sub>c \<tau>''\<close>] by metis
  hence "world_conc_exec tw (cs1 || cs2) (worldline2 t \<sigma> \<theta> def \<tau>'')"
    using des ex  by (meson world_conc_exec.intros)
  hence "tw'', cs2 \<Rightarrow>\<^sub>c tw_res"
    using des2 wcs1
    by (smt \<open>destruct_worldline (worldline2 t \<sigma> \<theta> def \<tau>') = (t, \<sigma>, \<gamma>, \<theta>, def, \<tau>')\<close> \<open>t , \<sigma> , \<gamma> , \<theta>,
    def \<turnstile> <cs2 , \<tau>'> \<longrightarrow>\<^sub>c \<tau>''\<close> assms(3) assms(5) b_conc_exec_deterministic fst_conv snd_conv
    world_conc_exec.intros world_conc_exec_cases)
  thus ?thesis
    by (smt assms(4) b_conc_exec_deterministic fst_conv snd_conv world_conc_exec_cases)
qed

lemma world_conc_exec_parallel2:
  assumes "conc_stmt_wf (cs1 || cs2)" and "nonneg_delay_conc (cs1 || cs2)"
  assumes "world_conc_exec tw   cs2 tw''"
  assumes "world_conc_exec tw'' cs1 tw' "
  assumes "tw, (cs1 || cs2) \<Rightarrow>\<^sub>c tw_res"
  shows "tw_res = tw'"
proof -
  have wf: "conc_stmt_wf (cs2 || cs1)" and nd: "nonneg_delay_conc (cs2 || cs1)"
    using assms unfolding conc_stmt_wf_def by auto
  have "world_conc_exec tw (cs2 || cs1) tw_res"
    using world_conc_exec_commute[OF _ _ assms(1)]
    by (smt assms(1) assms(5) parallel_comp_commute' world_conc_exec.intros world_conc_exec_cases)
  with world_conc_exec_parallel[OF wf nd] show ?thesis
    using assms(3) assms(4) by auto
qed

lemma parallel_valid:
  assumes "\<Turnstile> \<lbrace>P\<rbrace> c1 \<lbrace>R\<rbrace>" and "\<Turnstile> \<lbrace>R\<rbrace> c2 \<lbrace>Q\<rbrace>" and "conc_stmt_wf (c1 || c2)"
  assumes "nonneg_delay_conc (c1 || c2)"
  shows "\<Turnstile> \<lbrace>P\<rbrace> c1 || c2 \<lbrace>Q\<rbrace>"
  unfolding conc_hoare_valid_def
proof rule+
  fix tw tw':: "nat \<times> 'a worldline_init"
  assume "P tw \<and> tw , c1 || c2 \<Rightarrow>\<^sub>c tw'"
  hence "P tw" and "tw, c1 || c2 \<Rightarrow>\<^sub>c tw'"
    by auto
  then obtain t \<sigma> \<gamma> \<theta> \<tau> def \<tau>' where des: "destruct_worldline tw = (t, \<sigma>, \<gamma>, \<theta>, def, \<tau>)" and
    *: "t, \<sigma>, \<gamma>, \<theta>, def \<turnstile> <c1 || c2, \<tau>> \<longrightarrow>\<^sub>c \<tau>'" and w'_def: "worldline2 t \<sigma> \<theta> def \<tau>' = tw'" and
    ci: "context_invariant t \<sigma> \<gamma> \<theta> def \<tau>"
    using destruct_worldline_exist  by (smt world_conc_exec_cases worldline2_constructible)
  have "\<And>s. non_stuttering (to_trans_raw_sig \<tau>) \<sigma> s"
    using destruct_worldline_ensure_non_stuttering[OF des] by auto
  obtain \<tau>1 where "b_conc_exec t \<sigma> \<gamma> \<theta> def c1 \<tau> \<tau>1"
    using "*" by blast
  hence ci1: "context_invariant t \<sigma> \<gamma> \<theta> def \<tau>1"
    using b_conc_exec_preserves_context_invariant[OF _ ci] assms(4)  by auto
  have "\<And>n. n \<le> t \<Longrightarrow> \<tau> n = 0"
    using destruct_worldline_trans_zero_upto_now[OF des] by auto
  have "\<forall>s. non_stuttering (to_trans_raw_sig \<tau>1) \<sigma> s"
  proof
    fix s
    have "t, \<sigma>, \<gamma>, \<theta>, def \<turnstile> <c1, \<tau>> \<longrightarrow>\<^sub>c \<tau>1"
      using \<open>t , \<sigma> , \<gamma> , \<theta>, def \<turnstile> <c1 , \<tau>> \<longrightarrow>\<^sub>c \<tau>1\<close> by blast
    moreover have "non_stuttering (to_trans_raw_sig \<tau>) \<sigma> s"
      by (simp add: \<open>\<And>s. non_stuttering (to_trans_raw_sig \<tau>) \<sigma> s\<close>)
    moreover have "conc_stmt_wf c1" and "nonneg_delay_conc c1"
      using assms by auto
    ultimately show "non_stuttering (to_trans_raw_sig \<tau>1) \<sigma> s"
      using b_conc_exec_preserves_non_stuttering[OF _ _ `\<And>n. n \<le> t \<Longrightarrow> \<tau> n = 0`]
      by auto
  qed
  obtain \<tau>2 where "b_conc_exec t \<sigma> \<gamma> \<theta> def c2 \<tau> \<tau>2"
    using "*" by blast
  hence ci2: "context_invariant t \<sigma> \<gamma> \<theta> def \<tau>2"
    using b_conc_exec_preserves_context_invariant[OF _ ci] assms(4) by auto
  have \<tau>'_def: "b_conc_exec t \<sigma> \<gamma> \<theta> def c2 \<tau>1 \<tau>'"
    using b_conc_exec_sequential[OF assms(3) * `t, \<sigma>, \<gamma>, \<theta>, def \<turnstile> <c1, \<tau>> \<longrightarrow>\<^sub>c \<tau>1`]
    by auto
  define tw1 where "tw1 = worldline2 t \<sigma> \<theta> def \<tau>1"
  have "tw, c1 \<Rightarrow>\<^sub>c tw1"
    using des \<open>t , \<sigma> , \<gamma> , \<theta>, def \<turnstile> <c1 , \<tau>> \<longrightarrow>\<^sub>c \<tau>1\<close> tw1_def world_conc_exec.intros by blast
  hence "R tw1"
    using assms(1) `P tw` unfolding conc_hoare_valid_def  by meson
  have "\<forall>s. non_stuttering (to_trans_raw_sig \<theta>) def s"
    using des destruct_worldline_ensure_non_stuttering_hist_raw by blast
  hence des2: "destruct_worldline tw1 = (t, \<sigma>, \<gamma>, \<theta>, def, \<tau>1)"
    using destruct_worldline_correctness3[OF ci1 `\<forall>s. non_stuttering (to_trans_raw_sig \<tau>1) \<sigma> s`]
    unfolding tw1_def by auto
  moreover have "nonneg_delay_conc c2"
    using assms(4) by auto
  hence "tw1, c2 \<Rightarrow>\<^sub>c tw'"
    using des2
    apply (intro world_conc_exec.intros)
      apply assumption
     apply (rule \<tau>'_def)
    apply (simp add: w'_def)
    done
  with `R tw1` show "Q tw'"
    using assms(2) using conc_hoare_valid_def by metis
qed

lemma soundness_conc_hoare:
  assumes "\<turnstile> \<lbrace>P\<rbrace> c \<lbrace>Q\<rbrace>"
  assumes "conc_stmt_wf c" and "nonneg_delay_conc c"
  shows "\<Turnstile> \<lbrace>P\<rbrace> c \<lbrace>Q\<rbrace>"
  using assms
proof (induction rule:conc_hoare.induct)
  case (Single P sl ss Q)
  { fix tw  tw' :: "nat \<times> 'a worldline_init"
    assume as: "P tw \<and> (tw ,  process sl : ss \<Rightarrow>\<^sub>c tw')"
    then obtain t \<sigma> \<gamma> \<theta> \<tau> def \<tau>' where des: "destruct_worldline tw = (t, \<sigma>, \<gamma>, \<theta>, def, \<tau>)" and "P tw" and
      ex: "t, \<sigma>, \<gamma>, \<theta>, def \<turnstile> <process sl : ss, \<tau>> \<longrightarrow>\<^sub>c \<tau>'" and "(worldline2 t \<sigma> \<theta> def \<tau>') = tw'"
      by force
    have "fst tw = t"
      by (metis (no_types, lifting) des destruct_worldline_def fst_conv)
    have "nonneg_delay ss"
      using Single by auto
    have "disjnt sl \<gamma> \<or> \<not> disjnt sl \<gamma>"
      by auto
    moreover
    { assume "disjnt sl \<gamma>"
      hence "\<tau>' = \<tau>" using ex by auto
      hence "tw' = tw"
        using \<open>destruct_worldline tw = (t, \<sigma>, \<gamma>, \<theta>, def, \<tau>)\<close> \<open>(worldline2 t \<sigma> \<theta> def \<tau>') = tw'\<close>
        worldline2_constructible by (metis)
      with Single have "Q tw'"
        unfolding event_of_def  using \<open>P tw \<and> tw, process sl : ss \<Rightarrow>\<^sub>c tw'\<close>
        \<open>destruct_worldline tw = (t, \<sigma>, \<gamma>, \<theta>, def, \<tau>)\<close> \<open>disjnt sl \<gamma>\<close>  disjnt_sym by fastforce }
    moreover
    { assume "\<not> disjnt sl \<gamma>"
      hence "\<not> disjnt sl (event_of tw)"
        unfolding event_of_def using des `fst tw = t` by auto
      moreover have "tw, ss \<Rightarrow>\<^sub>s tw'"
        using as `\<not> disjnt sl \<gamma>`
      proof -
        have "t , \<sigma> , \<gamma> , \<theta>, def \<turnstile> < ss , \<tau>> \<longrightarrow>\<^sub>s \<tau>'"
          using \<open>\<not> disjnt sl \<gamma>\<close> ex by force
        then show ?thesis
          using \<open>worldline2 t \<sigma> \<theta> def \<tau>' = tw'\<close> des world_seq_exec.intros by blast
      qed
      ultimately have "Q tw'"
        using soundness_hoare2[OF Single(1) `nonneg_delay ss`] `P tw` `fst tw = t`
        unfolding seq_hoare_valid2_def by blast }
    ultimately have "Q tw'" by auto }
  then show ?case
    unfolding conc_hoare_valid_def by auto
next
  case (Parallel P cs\<^sub>1 R cs\<^sub>2 Q)
  hence "conc_stmt_wf cs\<^sub>1" and "conc_stmt_wf cs\<^sub>2"
    by (simp add: conc_stmt_wf_def)+
  moreover have "nonneg_delay_conc cs\<^sub>1" and "nonneg_delay_conc cs\<^sub>2"
    using Parallel by auto
  ultimately have " \<Turnstile> \<lbrace>P\<rbrace> cs\<^sub>1 \<lbrace>R\<rbrace>" and " \<Turnstile> \<lbrace>R\<rbrace> cs\<^sub>2 \<lbrace>Q\<rbrace>"
    using Parallel by auto
  then show ?case
    using parallel_valid Parallel by blast
next
  case (Parallel2 P cs\<^sub>2 R cs\<^sub>1 Q)
  hence "conc_stmt_wf cs\<^sub>1" and "conc_stmt_wf cs\<^sub>2"
    by (simp add: conc_stmt_wf_def)+
  moreover have "nonneg_delay_conc cs\<^sub>1" and "nonneg_delay_conc cs\<^sub>2"
    using Parallel2 by auto
  ultimately have cs2: " \<Turnstile> \<lbrace>P\<rbrace> cs\<^sub>2 \<lbrace>R\<rbrace>" and cs1: " \<Turnstile> \<lbrace>R\<rbrace> cs\<^sub>1 \<lbrace>Q\<rbrace>"
    using Parallel2 by auto
  have "conc_stmt_wf (cs\<^sub>2 || cs\<^sub>1)"
    using Parallel2(3) unfolding conc_stmt_wf_def by auto
  moreover have " nonneg_delay_conc (cs\<^sub>2 || cs\<^sub>1) "
    using Parallel2(7) by auto
  ultimately have "\<Turnstile> \<lbrace>P\<rbrace> cs\<^sub>2 || cs\<^sub>1 \<lbrace>Q\<rbrace>"
    using parallel_valid[OF cs2 cs1]   by auto
  thus ?case
    using world_conc_exec_commute[OF _ _ Parallel2(3)]  unfolding conc_hoare_valid_def
    by (smt Parallel2.prems(1) parallel_comp_commute' world_conc_exec.intros world_conc_exec_cases)
next
  case (Conseq' P' P c Q Q')
  then show ?case
    unfolding conc_hoare_valid_def by metis
next
  case (Conj2 P s Q1 Q2)
  then show ?case  by (simp add: conc_hoare_valid_def)
qed

definition wp_conc :: "'signal conc_stmt \<Rightarrow> 'signal assn2 \<Rightarrow> 'signal assn2" where
  "wp_conc cs Q = (\<lambda>tw. \<forall>tw'. (tw, cs \<Rightarrow>\<^sub>c tw') \<longrightarrow> Q tw')"

lemma wp_conc_single:
  "wp_conc (process sl : ss) Q =
  (\<lambda>tw. if disjnt sl (event_of tw) then Q tw else wp ss Q tw)"
  apply (rule ext)
  unfolding wp_conc_def wp_def
  by (smt conc_cases(1) event_of_def o_apply prod.sel(1) prod.sel(2) world_conc_exec_cases
  world_conc_exec_disjnt world_conc_exec_not_disjnt world_seq_exec.intros)

lemma wp_conc_parallel:
  assumes "conc_stmt_wf (cs1 || cs2)" and "nonneg_delay_conc (cs1 || cs2)"
  shows "wp_conc (cs1 || cs2) Q =  wp_conc cs1 (wp_conc cs2 Q)"
proof (rule ext, rule)
  fix x
  have "conc_stmt_wf cs1" and "conc_stmt_wf cs2"
    using assms  by (simp add: conc_stmt_wf_def)+
  have "nonneg_delay_conc cs1" and "nonneg_delay_conc cs2"
    using assms by auto
  assume "wp_conc (cs1 || cs2) Q x "
  hence "(\<forall>tw'. x , cs1 || cs2 \<Rightarrow>\<^sub>c tw' \<longrightarrow> Q tw')"
    unfolding wp_conc_def by auto
  thus" wp_conc cs1 (wp_conc cs2 Q) x"
    unfolding wp_conc_def sym[OF world_conc_exec_eq_world_conc_exec_alt[OF assms]]
    sym[OF world_conc_exec_eq_world_conc_exec_alt[OF `conc_stmt_wf cs1` `nonneg_delay_conc cs1`]]
    sym[OF world_conc_exec_eq_world_conc_exec_alt[OF `conc_stmt_wf cs2` `nonneg_delay_conc cs2`]]
    using world_conc_exec_alt.intros(3) by blast
next
  fix x
  have "conc_stmt_wf cs1" and "conc_stmt_wf cs2"
    using assms  by (simp add: conc_stmt_wf_def)+
  have "nonneg_delay_conc cs1" and "nonneg_delay_conc cs2"
    using assms by auto
  assume "wp_conc cs1 (wp_conc cs2 Q) x"
  hence "\<forall>tw tw'. x , cs1 \<Rightarrow>\<^sub>c tw \<and> tw , cs2 \<Rightarrow>\<^sub>c tw' \<longrightarrow> Q tw'"
    unfolding wp_conc_def by meson
  thus "wp_conc (cs1 || cs2) Q x"
    unfolding wp_conc_def sym[OF world_conc_exec_eq_world_conc_exec_alt[OF assms]]
    by (metis (mono_tags, hide_lams) \<open>\<And>tw. world_conc_exec tw (cs1 || cs2) = world_conc_exec_alt tw
    (cs1 || cs2)\<close> \<open>wp_conc cs1 (wp_conc cs2 Q) x\<close> assms(1) assms(2) conc_hoare_valid_def
    parallel_valid wp_conc_def)
qed

lemma wp_conc_parallel2:
  assumes "conc_stmt_wf (cs1 || cs2)" and "nonneg_delay_conc (cs1 || cs2)"
  shows "wp_conc (cs1 || cs2) Q =  wp_conc cs2 (wp_conc cs1 Q)"
proof (rule ext, rule)
  fix x
  have "conc_stmt_wf cs1" and "conc_stmt_wf cs2"
    using assms  by (simp add: conc_stmt_wf_def)+
  have "nonneg_delay_conc cs1" and "nonneg_delay_conc cs2"
    using assms by auto
  assume "wp_conc (cs1 || cs2) Q x"
  hence "\<forall>tw'. x , cs1 || cs2 \<Rightarrow>\<^sub>c tw' \<longrightarrow> Q tw'"
    unfolding wp_conc_def by auto
  thus" wp_conc cs2 (wp_conc cs1 Q) x"
    unfolding wp_conc_def sym[OF world_conc_exec_eq_world_conc_exec_alt[OF assms]]
    sym[OF world_conc_exec_eq_world_conc_exec_alt[OF `conc_stmt_wf cs1` `nonneg_delay_conc cs1`]]
    sym[OF world_conc_exec_eq_world_conc_exec_alt[OF `conc_stmt_wf cs2` `nonneg_delay_conc cs2`]]
    using assms(1) assms(2) world_conc_exec_alt.intros(4) world_conc_exec_alt_imp_world_conc_exec
    by blast
next
  fix x
  have "conc_stmt_wf cs1" and "conc_stmt_wf cs2"
    using assms  by (simp add: conc_stmt_wf_def)+
  have "nonneg_delay_conc cs1" and "nonneg_delay_conc cs2"
    using assms by auto
  have "conc_stmt_wf (cs2 || cs1)" and "nonneg_delay_conc (cs2 || cs1)"
    using assms
    by (metis conc_stmt_wf_def disjoint_iff_not_equal distinct_append signals_from.simps(2))
       (simp add: \<open>nonneg_delay_conc cs1\<close> \<open>nonneg_delay_conc cs2\<close>)
  assume "wp_conc cs2 (wp_conc cs1 Q) x"
  hence "\<forall>tw tw'. x , cs2 \<Rightarrow>\<^sub>c tw \<and> tw , cs1 \<Rightarrow>\<^sub>c tw' \<longrightarrow> Q tw'"
    unfolding wp_conc_def  by meson
  hence "wp_conc (cs2 || cs1) Q x"
    unfolding wp_conc_def
    using sym[OF world_conc_exec_eq_world_conc_exec_alt[OF `conc_stmt_wf (cs2 || cs1)` `nonneg_delay_conc (cs2 || cs1)`]]
    by (metis \<open>conc_stmt_wf (cs2 || cs1)\<close> \<open>nonneg_delay_conc (cs2 || cs1)\<close> wp_conc_def wp_conc_parallel)
  thus "wp_conc (cs1 || cs2) Q x"
    unfolding wp_conc_def by (smt assms(1) parallel_comp_commute' world_conc_exec.intros world_conc_exec_cases)
qed

lemma wp_conc_is_pre:
  assumes "conc_stmt_wf cs" and "nonneg_delay_conc cs"
  shows "\<turnstile> \<lbrace>wp_conc cs Q\<rbrace> cs \<lbrace>Q\<rbrace>"
  using assms
proof (induction cs arbitrary:Q)
  case (Bpar cs1 cs2)
  hence "conc_stmt_wf cs1" and "conc_stmt_wf cs2" and "nonneg_delay_conc cs1" and "nonneg_delay_conc cs2"
    by auto
  hence "\<And>Q.  \<turnstile> \<lbrace>wp_conc cs1 Q\<rbrace> cs1 \<lbrace>Q\<rbrace>" and "\<And>Q.  \<turnstile> \<lbrace>wp_conc cs2 Q\<rbrace> cs2 \<lbrace>Q\<rbrace>"
    using Bpar(1-2) by auto
  then show ?case
    unfolding wp_conc_parallel[OF Bpar(3-4)]
    by (auto intro!: Parallel simp add: Bpar)
next
  case (Bsingle sl ss)
  hence "nonneg_delay ss"
    by auto
  then show ?case  unfolding wp_conc_single
    by (auto intro!: Single simp add: hoare_sound_complete seq_hoare_valid2_def wp_def)
qed

lemma conc_hoare_complete:
  assumes "conc_stmt_wf cs" and "nonneg_delay_conc cs"
  assumes "\<Turnstile> \<lbrace>P\<rbrace> cs \<lbrace>Q\<rbrace>" shows "\<turnstile> \<lbrace>P\<rbrace> cs \<lbrace>Q\<rbrace>"
proof (rule strengthen_pre_conc_hoare)
  show " \<forall>tw. P tw \<longrightarrow> wp_conc cs Q tw" using assms
    by (metis conc_hoare_valid_def wp_conc_def)
next
  show "\<turnstile> \<lbrace>wp_conc cs Q\<rbrace> cs \<lbrace>Q\<rbrace>"
    using assms by (intro wp_conc_is_pre)
qed

corollary conc_hoare_sound_and_complete:
  assumes "conc_stmt_wf cs" and "nonneg_delay_conc cs"
  shows "\<turnstile> \<lbrace>P\<rbrace> cs \<lbrace>Q\<rbrace> \<longleftrightarrow> \<Turnstile> \<lbrace>P\<rbrace> cs \<lbrace>Q\<rbrace>"
  using conc_hoare_complete soundness_conc_hoare assms by auto

lemma push_rem_curr_trans_purge_raw:
  assumes "\<And>n. n \<le> t \<Longrightarrow> \<tau> n = 0"
  shows "(purge_raw \<tau> t dly sig def val)(t:=0) = purge_raw (\<tau>(t:=0)) t dly sig def val"
proof -
  have "\<tau> (t:=0) = \<tau>"
    using assms by auto
  hence **: "purge_raw (\<tau>(t:=0)) t dly sig def val = purge_raw \<tau> t dly sig def val"
    by auto
  let ?s1 = "signal_of def \<tau> sig t"
  let ?s2 = "signal_of def \<tau> sig (t + dly)"
  let ?k2 = "inf_time (to_trans_raw_sig \<tau>) sig (t + dly)"
  have "(?s1 = val \<or> ?s2 \<noteq> val) \<or> (?s1 \<noteq> val \<and> ?s2 = val)"
    by auto
  moreover
  { assume "?s1 = val \<or> ?s2 \<noteq> val"
    hence *: "purge_raw \<tau> t dly sig def val = override_on \<tau> (\<lambda>n. (\<tau> n)(sig := None)) {t<..t + dly}"
      unfolding purge_raw_def by auto
    hence "(purge_raw \<tau> t dly sig def val)(t:=0) = (override_on \<tau> (\<lambda>n. (\<tau> n)(sig := None)) {t<..t + dly})(t:=0)"
      by auto
    also have "... = override_on \<tau> (\<lambda>n. (\<tau> n)(sig := None)) {t<..t + dly}"
      by (metis \<open>\<tau>(t := 0) = \<tau>\<close> \<open>purge_raw \<tau> t dly sig def val = override_on \<tau> (\<lambda>n. (\<tau> n)(sig :=
      None)) {t<..t + dly}\<close> dual_order.refl fun_upd_idem_iff purge_raw_before_now_unchanged)
    also have "... = purge_raw \<tau> t dly sig def val"
      using * by auto
    finally have ?thesis
      using ** by auto }
  moreover
  { assume "?s1 \<noteq> val \<and> ?s2 = val"
    hence "purge_raw \<tau> t dly sig def val = override_on \<tau> (\<lambda>n. (\<tau> n)(sig := None)) ({t<..<the ?k2} \<union> {the ?k2<..t + dly})"
      (is "?lhs = ?rhs") unfolding purge_raw_def Let_def by auto
    hence "?lhs(t:=0) = ?rhs(t:=0)"
      by auto
    have "t < the ?k2"
    proof -
      have "?s1 \<noteq> val" and "?s2 = (val)"
        using `?s1 \<noteq>  val \<and> ?s2 = val` by auto
      have "\<exists>n>t. n \<le> t + dly \<and> \<tau> n sig = Some val"
        using switch_signal_ex_mapping[OF `?s1 \<noteq> val` `?s2 = (val)`] assms
        by (simp add: zero_fun_def)
      hence "?k2 \<noteq> None"
        by (metis add.commute inf_time_noneE2 option.discI semiring_normalization_rules(24)
        to_trans_raw_sig_def zero_option_def)
      then obtain k where "?k2 = Some k"
        by auto
      hence "\<tau> k sig \<noteq> None"
        by (metis domIff dom_def inf_time_some_exists keys_def to_trans_raw_sig_def zero_option_def)
      hence "t < k"
        using assms  by (metis (full_types) not_less zero_fun_def zero_option_def)
      thus ?thesis
        by (simp add: \<open>inf_time (to_trans_raw_sig \<tau>) sig (t + dly) = Some k\<close>)
    qed
    hence "?rhs(t:=0) = ?rhs"
      by (metis \<open>\<tau>(t := 0) = \<tau>\<close> \<open>purge_raw \<tau> t dly sig def val = override_on \<tau> (\<lambda>n. (\<tau> n)(sig :=
      None)) ({t<..<the (inf_time (to_trans_raw_sig \<tau>) sig (t + dly))} \<union> {the (inf_time
      (to_trans_raw_sig \<tau>) sig (t + dly))<..t + dly})\<close> fun_upd_idem_iff order.order_iff_strict
      purge_raw_before_now_unchanged)
    also have "... = ?lhs"
      using `?lhs = ?rhs` by auto
    finally have "?lhs(t:=0) = ?lhs"
      using \<open>purge_raw \<tau> t dly sig def val = override_on \<tau> (\<lambda>n. (\<tau> n)(sig := None)) ({t<..<the
      (inf_time (to_trans_raw_sig \<tau>) sig (t + dly))} \<union> {the (inf_time (to_trans_raw_sig \<tau>) sig (t +
      dly))<..t + dly})\<close> by auto
    hence ?thesis
      by (simp add: \<open>\<tau>(t := 0) = \<tau>\<close>) }
  ultimately show ?thesis
    by auto
qed

lemma post_necessary_raw_rem_curr_trans:
  assumes "context_invariant t \<sigma> \<gamma> \<theta> def \<tau>"
  shows "post_necessary_raw n \<tau> t s val (\<sigma> s) \<longleftrightarrow> post_necessary_raw n (\<tau>(t:=0)) t s val (\<sigma> s)"
proof
  assume "post_necessary_raw n \<tau> t s val (\<sigma> s)"
  hence "(\<exists>i val'. i \<le> t + n \<and>  \<tau> i s = Some val' \<and> val' \<noteq> val \<and> (\<forall>j>i. j \<le> t + n \<longrightarrow>  \<tau> j s = None))
                                      \<or>   (\<forall>i. i \<le> t + n \<longrightarrow>  \<tau> i s = None) \<and> val \<noteq> (\<sigma> s)"
    (is "?case1 \<or> ?case2")
    unfolding post_necessary_raw_correctness2 by blast
  moreover
  { assume "?case1"
    then obtain i val' where "i \<le> t + n" and " \<tau> i s = Some val' \<and> val' \<noteq> val \<and> (\<forall>j>i. j \<le> t + n \<longrightarrow>  \<tau> j s = None) "
      by auto
    hence "t < i"
      using assms unfolding context_invariant_def
      by (metis domI domIff not_le_imp_less zero_fun_def zero_option_def)
    hence "(\<exists>i. i \<le> t + n \<and>  (\<tau>(t:=0)) i s = Some val' \<and> val' \<noteq> val \<and> (\<forall>j>i. j \<le> t + n \<longrightarrow>  (\<tau>(t:=0)) j s = None))"
      using `i \<le> t + n` ` \<tau> i s = Some val' \<and> val' \<noteq> val \<and> (\<forall>j>i. j \<le> t + n \<longrightarrow>  \<tau> j s = None)`
      by (metis fun_upd_apply nat_less_le zero_fun_def zero_option_def)
    hence "post_necessary_raw n (\<tau>(t:=0)) t s val (\<sigma> s)"
      by (metis (no_types, lifting) \<open>post_necessary_raw n \<tau> t s val (\<sigma> s)\<close> assms context_invariant_def fun_upd_idem_iff less_irrefl_nat not_less) }
  moreover
  { assume "?case2"
    hence "(\<forall>i. i \<le> t + n \<longrightarrow>  (\<tau>(t:=0)) i s = None) \<and> val \<noteq> \<sigma> s"
      by (auto simp add: zero_fun_def zero_option_def)
    hence "post_necessary_raw n (\<tau>(t:=0)) t s val (\<sigma> s)"
      by (metis signal_of_def zero_option_def) }
  ultimately show "post_necessary_raw n (\<tau>(t:=0)) t s val (\<sigma> s)"
    by auto
next
  assume "post_necessary_raw n (\<tau>(t:=0)) t s val (\<sigma> s)"
  hence "(\<exists>i val'. i \<le> t + n \<and>  (\<tau>(t:=0)) i s = Some val' \<and> val' \<noteq> val \<and> (\<forall>j>i. j \<le> t + n \<longrightarrow>  (\<tau>(t:=0)) j s = None))
                                      \<or>   (\<forall>i. i \<le> t + n \<longrightarrow>  (\<tau>(t:=0)) i s = None) \<and> val \<noteq> (\<sigma> s)"
    (is "?case1 \<or> ?case2") unfolding post_necessary_raw_correctness2 by auto
  moreover
  { assume "?case1"
    then obtain i val' where "i \<le> t + n" and " ((\<tau>(t:=0)) i s = Some val' \<and> val' \<noteq> val \<and> (\<forall>j>i. j \<le> t + n \<longrightarrow>  (\<tau>(t:=0)) j s = None)) "
      by auto
    hence "i \<ge> t"
      using assms unfolding context_invariant_def
      by (metis fun_upd_triv le_refl nat_le_linear option.discI zero_fun_def zero_option_def)
    hence "i \<noteq> t"
      by (metis \<open>(\<tau>(t := 0)) i s = Some val' \<and> val' \<noteq> val \<and> (\<forall>j>i. j \<le> t + n \<longrightarrow> (\<tau>(t := 0)) j s = None)\<close>
      fun_upd_apply option.distinct(1) zero_fun_def zero_option_def)
    hence " \<tau> i s = Some val' \<and> val' \<noteq> val \<and> (\<forall>j>i. j \<le> t + n \<longrightarrow>  \<tau> j s = None)"
      using ` (\<tau>(t:=0)) i s = Some val' \<and> val' \<noteq> val \<and> (\<forall>j>i. j \<le> t + n \<longrightarrow>  (\<tau>(t:=0)) j s = None)` `i \<ge> t`
      by auto
    with `i \<ge> t` and `i \<le> t + n` have "post_necessary_raw n ( \<tau>) t s val (\<sigma> s)"
      by (metis (no_types, lifting) \<open>post_necessary_raw n (\<tau>(t := 0)) t s val (\<sigma> s)\<close> assms
      context_invariant_def fun_upd_idem_iff order_refl) }
  moreover
  { assume "?case2"
    have " \<tau> t s = None \<or>  \<tau> t s = Some (\<sigma> s)"
      using assms unfolding context_invariant_def by (simp add: zero_fun_def zero_option_def)
    moreover
    { assume " \<tau> t s = None"
      with `?case2` have "(\<forall>i\<ge>t. i \<le> t + n \<longrightarrow>  \<tau> i s = None) \<and> val \<noteq> \<sigma> s"
        by (metis (full_types) fun_upd_apply)
      hence "post_necessary_raw n ( \<tau>) t s val (\<sigma> s)"
        by (metis (mono_tags, lifting) \<open>post_necessary_raw n (\<tau>(t := 0)) t s val (\<sigma> s)\<close> assms
        context_invariant_def dual_order.refl fun_upd_idem) }
    moreover
    { assume " \<tau> t s = Some (\<sigma> s)"
      hence "(\<exists>i val'. i \<le> t + n \<and>  \<tau> i s = Some val' \<and> val' \<noteq> val \<and> (\<forall>j>i. j \<le> t + n \<longrightarrow>  \<tau> j s = None))"
        using `?case2`
        apply(intro exI[where x="t"])
        unfolding rem_curr_trans_def  using le_eq_less_or_eq context_invariant_def by auto
      hence "post_necessary_raw n ( \<tau>) t s val (\<sigma> s)"
        unfolding post_necessary_raw_correctness2 by auto }
    ultimately have "post_necessary_raw n ( \<tau>) t s val (\<sigma> s)"
      by auto }
  ultimately show "post_necessary_raw n ( \<tau>) t s val (\<sigma> s)"
    by auto
qed

lemma context_invariant_purged:
  assumes "context_invariant t \<sigma> \<gamma> \<theta> def \<tau>"
  shows "context_invariant t \<sigma> \<gamma> \<theta> def (purge_raw \<tau> t dly sig (def sig) val)"
proof -
  have "\<forall>n\<le>t.  \<tau> n = 0" and "\<gamma> = {s. \<sigma> s \<noteq> signal_of (def s) \<theta> s (t - 1)}" and "\<forall>n\<ge>t.  \<theta> n = 0"
    using assms unfolding context_invariant_def by auto
  moreover hence "\<forall>n < t. (purge_raw \<tau> t dly sig (def sig) val) n = 0"
    by (simp add: purge_preserve_trans_removal)
  ultimately show ?thesis
    unfolding context_invariant_def by (metis purge_raw_before_now_unchanged)
qed

lemma b_seq_exec_mono_wrt_rem_curr_trans:
  assumes "t, \<sigma>, \<gamma>, \<theta>, def \<turnstile> < ss, \<tau>> \<longrightarrow>\<^sub>s \<tau>'"
  assumes "nonneg_delay ss"
  assumes "context_invariant t \<sigma> \<gamma> \<theta> def \<tau>"
  shows "t, \<sigma>, \<gamma>, \<theta>, def \<turnstile> < ss, \<tau>(t:=0)> \<longrightarrow>\<^sub>s \<tau>'(t:=0)"
  using assms
proof (induction rule: b_seq_exec.inducts)
  case (1 t \<sigma> \<gamma> \<theta> def \<tau>)
  then show ?case
    using b_seq_exec.intros(1) by blast
next
  case (2 t \<sigma> \<gamma> \<theta> def ss1 \<tau> \<tau>'' ss2 \<tau>')
  then show ?case
    using b_seq_exec_preserves_context_invariant
    by (metis b_seq_exec.intros(2) nonneg_delay.simps(2))
next
  case (3 t \<sigma> \<gamma> \<theta> def guard ss1 \<tau> \<tau>' ss2)
  then show ?case
    by (metis b_seq_exec.intros(3) nonneg_delay.simps(3))
next
  case (4 t \<sigma> \<gamma> \<theta> def guard ss2 \<tau> \<tau>' ss1)
  then show ?case
    by (metis  b_seq_exec.intros(4) nonneg_delay.simps(3))
next
  case (5 t \<sigma> \<gamma> \<theta> def e x sig \<tau> dly \<tau>')
  hence "\<tau>' = trans_post_raw sig x (\<sigma> sig) \<tau> t dly" and "0 < dly"
    using "5.prems"(1) by auto
  hence "\<tau>'(t:=0) = (trans_post_raw sig x (\<sigma> sig) \<tau> t dly)(t:=0)"
    by auto
  also have "... = trans_post_raw sig x (\<sigma> sig) (\<tau>(t:=0)) t dly"
    using `0 < dly` post_necessary_raw_rem_curr_trans[OF `context_invariant t \<sigma> \<gamma> \<theta> def \<tau>`]
  proof -
    have f1: "\<tau> t = 0"
      by (meson "5.prems"(2) context_invariant_def le_refl)
    have "\<forall>f. trans_post_raw sig x (\<sigma> sig) f t dly t = f t"
      by (metis (no_types) "5.hyps"(1) "5.prems"(1) b_seq_exec.intros(5) nonneg_delay_same)
    then show ?thesis
      using f1 by (metis (no_types) fun_upd_triv)
  qed
  finally show ?case
    by (metis \<open>t , \<sigma> , \<gamma> , \<theta>, def \<turnstile> e \<longrightarrow>\<^sub>b x\<close> b_seq_exec.intros(5))
next
  case (6 t \<sigma> \<gamma> \<theta> def e x sig \<tau> dly \<tau>')
  hence \<tau>'_def: "\<tau>' = inr_post_raw sig x (\<sigma> sig) \<tau> t dly" and "0 < dly"
    using "6.prems"(1) by auto
  have "context_invariant t \<sigma> \<gamma> \<theta> def (purge_raw \<tau> t dly sig (\<sigma> sig) x)"
    using context_invariant_purged `context_invariant t \<sigma> \<gamma> \<theta> def \<tau>`
    by (simp add: context_invariant_def purge_preserve_trans_removal_nonstrict)
  have "\<tau>' = trans_post_raw sig x (\<sigma> sig) (purge_raw \<tau> t dly sig (\<sigma> sig) x) t dly"
    using \<tau>'_def unfolding inr_post_raw_def by auto
  hence "\<tau>'(t:=0) = (trans_post_raw sig x (\<sigma> sig) ((purge_raw \<tau> t dly sig (\<sigma> sig) x)) t dly)(t:=0)"
    by auto
  also have "... = trans_post_raw sig x (\<sigma> sig) ((purge_raw \<tau> t dly sig (\<sigma> sig) x)(t:=0)) t dly"
    using `0 < dly` post_necessary_raw_rem_curr_trans[OF `context_invariant t \<sigma> \<gamma> \<theta> def (purge_raw \<tau> t dly sig (\<sigma> sig) x)`]
  proof -
    have f1: "\<forall>n. purge_raw \<tau> t dly sig (\<sigma> sig) x n = 0 \<or> \<not> n \<le> t"
      by (meson \<open>context_invariant t \<sigma> \<gamma> \<theta> def (purge_raw \<tau> t dly sig (\<sigma> sig) x)\<close> context_invariant_def)
    have "\<forall>f n a. trans_post_raw a x (\<sigma> a) f t n t = f t \<or> \<not> nonneg_delay (Bassign_trans a e n)"
      by (metis (no_types) "6.hyps"(1) b_seq_exec.intros(5) nonneg_delay_same)
    then show ?thesis
      using f1 by (metis \<open>0 < dly\<close> dual_order.refl fun_upd_triv nonneg_delay.simps(4))
  qed
  also have "... = trans_post_raw sig x (\<sigma> sig) (purge_raw (\<tau>(t:=0)) t dly sig (\<sigma> sig) x) t dly"
    unfolding push_rem_curr_trans_purge_raw
    by (metis (no_types, lifting) "6.prems" context_invariant_def push_rem_curr_trans_purge_raw)
  also have "... = inr_post_raw sig x (\<sigma> sig) (\<tau>(t:=0)) t dly"
    unfolding inr_post_raw_def by auto
  finally show ?case
    by (metis \<open>t , \<sigma> , \<gamma> , \<theta>, def \<turnstile> e \<longrightarrow>\<^sub>b x\<close> b_seq_exec.intros(6))
next
  case (7 t \<sigma> \<gamma> \<theta> def exp x exp' ss \<tau> \<tau>' choices)
  then show ?case
    using b_seq_exec.intros(7) by force
next
  case (8 t \<sigma> \<gamma> \<theta> def exp x exp' x' choices \<tau> \<tau>' ss)
  then show ?case
    using b_seq_exec.intros(8) by force
next
  case (9 t \<sigma> \<gamma> \<theta> def ss \<tau> \<tau>' exp choices)
  then show ?case
    by (simp add: b_seq_exec.intros(9))
next
  case (10 t \<sigma> \<gamma> \<theta> def exp \<tau>)
  then show ?case
    by (simp add: b_seq_exec.intros(10))
qed

text \<open>The following lemma is based on the assumption (premise) that @{term "conc_stmt_wf cs"}. This
is because we want to employ the theorem @{thm "b_conc_exec_sequential"} where executing two parallel
processes can be seen as executing two sequential processes. This is, of course, relies on the
assumption that both processes do not modify the same signals.

A more fundamental question arises: can we prove this theorem without this well-formedness premise
and this theorem? We certainly would need to reason about @{term "clean_zip"} as this is the
primitive operation for handling parallel execution.\<close>

lemma b_conc_exec_mono_wrt_rem_curr_trans:
  assumes "t, \<sigma>, \<gamma>, \<theta>, def \<turnstile> <cs, \<tau>> \<longrightarrow>\<^sub>c \<tau>'"
  assumes "nonneg_delay_conc cs" and "conc_stmt_wf cs"
  assumes "context_invariant t \<sigma> \<gamma> \<theta> def \<tau>"
  shows "t, \<sigma>, \<gamma>, \<theta>, def  \<turnstile> <cs, \<tau>(t:=0)> \<longrightarrow>\<^sub>c (\<tau>'(t:=0))"
  using assms
proof (induction cs arbitrary: \<tau> \<tau>')
  case (Bpar cs1 cs2)
  then obtain \<tau>1 where \<tau>1_def: "b_conc_exec t \<sigma> \<gamma> \<theta> def cs1 \<tau> \<tau>1"
    by blast
  hence **: "t , \<sigma> , \<gamma> , \<theta>, def \<turnstile> <cs1 , \<tau>(t:=0)> \<longrightarrow>\<^sub>c \<tau>1(t:=0)"
    using Bpar unfolding conc_stmt_wf_def by fastforce
  have *: "b_conc_exec t \<sigma> \<gamma> \<theta> def cs2 \<tau>1 \<tau>'"
    using b_conc_exec_sequential[OF `conc_stmt_wf (cs1 || cs2)`] Bpar(3) \<tau>1_def by auto
  with Bpar have "t , \<sigma> , \<gamma> , \<theta>, def \<turnstile> <cs2 , \<tau>1(t:=0)> \<longrightarrow>\<^sub>c \<tau>'(t:=0)"
    unfolding conc_stmt_wf_def
    by (metis \<tau>1_def b_conc_exec_preserves_context_invariant distinct_append
    nonneg_delay_conc.simps(2) signals_from.simps(2))
  then show ?case
    using * Bpar(3)
    by (metis (mono_tags, hide_lams) Bpar.prems(2) Bpar.prems(4) context_invariant_def fun_upd_triv
    nonneg_delay_conc_same order_refl)
next
  case (Bsingle sl ss)
  hence "nonneg_delay ss"
    by auto
  have "disjnt sl \<gamma> \<or> \<not> disjnt sl \<gamma>"
    by auto
  moreover
  { assume "disjnt sl \<gamma>"
    hence ?case
      using Bsingle.prems(1) b_conc_exec.intros(1) by blast }
  moreover
  { assume "\<not> disjnt sl \<gamma>"
    hence "t, \<sigma>, \<gamma>, \<theta>, def \<turnstile> < ss, \<tau>> \<longrightarrow>\<^sub>s \<tau>'"
      using Bsingle by auto
    hence "t, \<sigma>, \<gamma>, \<theta>, def \<turnstile> < ss, \<tau>(t:=0)> \<longrightarrow>\<^sub>s \<tau>'(t:=0)"
      using b_seq_exec_mono_wrt_rem_curr_trans[OF _ `nonneg_delay ss`]  by (simp add: Bsingle.prems(4))
    hence ?case
      using `\<not> disjnt sl \<gamma>` by (metis b_conc_exec.simps(1)) }
  ultimately show ?case by auto
qed

lemma worldline_rem_curr_trans_eq:
  assumes "\<And>s. s \<in> dom (\<tau> t) \<Longrightarrow> \<sigma> s = the (\<tau> t s)"
  assumes "\<And>n. n < t \<Longrightarrow> \<tau> n = 0"
  shows "worldline2 t \<sigma> \<theta> def \<tau> = worldline2 t \<sigma> \<theta> def (\<tau>(t:=0))"
  using assms unfolding worldline2_def worldline_raw_def
  using signal_of_rem_curr_trans_at_t[where \<sigma>="\<sigma>" and \<tau>="\<tau>", OF assms]
  by presburger

lemma worldline2_constructible_rem_curr_trans:
  fixes tw :: "nat \<times> 'signal worldline_init"
  assumes "destruct_worldline tw = (t, \<sigma>, \<gamma>, \<theta>, def, \<tau>)"
  defines "\<tau>' \<equiv> \<tau>(t:=0)"
  shows "tw = worldline2 t \<sigma> \<theta> def \<tau>' \<and> context_invariant t \<sigma> \<gamma> \<theta> def \<tau>'"
proof -
  have "fst tw = t" and "tw = worldline2 t \<sigma> \<theta> def \<tau> \<and> context_invariant t \<sigma> \<gamma> \<theta> def \<tau>"
    using worldline2_constructible[OF assms(1)] by auto
  hence "\<And>n. n \<le> t \<Longrightarrow>  \<tau> n = 0"
    and " tw = worldline2 t \<sigma> \<theta> def \<tau>"
    and " context_invariant t \<sigma> \<gamma> \<theta> def \<tau>"
    unfolding context_invariant_def by auto
  hence "tw = worldline2 t \<sigma> \<theta> def \<tau>'"
    unfolding \<tau>'_def by (metis fun_upd_triv order_refl)
  moreover have "context_invariant t \<sigma> \<gamma> \<theta> def \<tau>'"
    unfolding \<tau>'_def using context_invariant_rem_curr_trans[OF `context_invariant t \<sigma> \<gamma> \<theta> def \<tau>`]
    by auto
  ultimately show ?thesis
    by auto
qed

inductive world_conc_exec2 :: "nat \<times> 'signal worldline_init \<Rightarrow> 'signal conc_stmt \<Rightarrow> nat \<times> 'signal worldline_init \<Rightarrow> bool" where
  "   destruct_worldline tw = (t, \<sigma>, \<gamma>, \<theta>, def, \<tau>)
  \<Longrightarrow> b_conc_exec t \<sigma> \<gamma> \<theta> def c (\<tau>(t := 0)) \<tau>'
  \<Longrightarrow> worldline2 t \<sigma> \<theta> def \<tau>' = tw'
  \<Longrightarrow> world_conc_exec2 tw c tw'"

inductive_cases world_conc_exec2_cases [elim!] : "world_conc_exec2 tw c tw'"

lemma world_conc_exec_rem_curr_trans_eq_only_if:
  assumes "nonneg_delay_conc c" and "conc_stmt_wf c"
  assumes "world_conc_exec tw c tw'"
  shows   "world_conc_exec2 tw c tw'"
proof -
  obtain t \<sigma> \<gamma> \<theta> def \<tau> \<tau>' where des: "destruct_worldline tw = (t, \<sigma>, \<gamma>, \<theta>, def, \<tau>)" and  ex: "t, \<sigma>, \<gamma>, \<theta>, def \<turnstile> <c, \<tau>> \<longrightarrow>\<^sub>c \<tau>'"
    and ci: "context_invariant t \<sigma> \<gamma> \<theta> def \<tau>"
    using destruct_worldline_exist worldline2_constructible assms(3) by blast
  hence ex2: "t, \<sigma>, \<gamma>, \<theta>, def \<turnstile> <c, \<tau>(t:=0)> \<longrightarrow>\<^sub>c (\<tau>'(t:=0))"
    using b_conc_exec_mono_wrt_rem_curr_trans[OF ex] assms(1-2) by blast
  moreover have "context_invariant t \<sigma> \<gamma> \<theta> def \<tau>'"
    using b_conc_exec_preserves_context_invariant[OF ex ci assms(1)] by auto
  ultimately have "worldline2 t \<sigma> \<theta> def \<tau>' = worldline2 t \<sigma> \<theta> def (\<tau>'(t:=0))"
    using worldline_rem_curr_trans_eq unfolding context_invariant_def by (simp add: fun_upd_idem)
  thus ?thesis
    using des ex ex2
    by (smt assms(3) destruct_worldline_no_trans_at_t fun_upd_idem world_conc_exec2.intros world_conc_exec_cases)
qed

subsection \<open>A sound and complete Hoare logic for VHDL's simulation\<close>

definition worldline_of_history :: "'signal state \<Rightarrow> 'signal trans_raw \<Rightarrow> 'signal worldline"
  where "worldline_of_history def \<theta> s t \<equiv> signal_of (def s) \<theta> s t"

inductive world_sim_fin :: "nat \<times> 'signal worldline_init \<Rightarrow> nat \<Rightarrow> 'signal conc_stmt \<Rightarrow> nat \<times> 'signal worldline_init \<Rightarrow> bool"
  (" _, _, _ \<Rightarrow>\<^sub>S _") where
  "    destruct_worldline tw = (t, \<sigma>, \<gamma>, \<theta>, def, \<tau>)
   \<Longrightarrow> T, t, \<sigma>, \<gamma>, \<theta>, def \<turnstile> <cs, \<tau>> \<leadsto> (t', \<sigma>', \<theta>', \<tau>')
   \<Longrightarrow> worldline_raw t' \<sigma>' \<theta>' def \<tau>' = w'
   \<Longrightarrow> tw, T, cs \<Rightarrow>\<^sub>S (t', w')"

lemma
  assumes "T < fst tw"
  shows "tw, T, cs \<Rightarrow>\<^sub>S tw"
proof -
  obtain t \<sigma> \<gamma> \<theta> def \<tau> where des: "destruct_worldline tw = (t, \<sigma>, \<gamma>, \<theta>, def, \<tau>)"
    by (meson destruct_worldline_def)
  hence "fst tw = t"
    unfolding destruct_worldline_def Let_def by auto
  with assms have "T < t"
    by auto
  hence sim: "T, t, \<sigma>, \<gamma>, \<theta>, def \<turnstile> <cs, \<tau>> \<leadsto> (t, \<sigma>, \<theta>, \<tau>)"
    by (intro b_simulate_fin.intros(3)) auto
  define w' where "w' = worldline_raw (max (T + 1) t) \<sigma> \<theta> def \<tau>"
  have "tw = worldline2 t \<sigma> \<theta> def \<tau>" and " context_invariant t \<sigma> \<gamma> \<theta> def \<tau>"
    using worldline2_constructible[OF des] by auto
  hence "snd tw = worldline_raw t \<sigma> \<theta> def \<tau>"
    unfolding worldline2_def by auto
  also have "... = w'"
    unfolding w'_def worldline_raw_def using `T < t`
    by fastforce
  finally have "snd tw = w'"
    by auto
  moreover have "max T t = t"
    using `T < t` by auto
  ultimately show ?thesis
    using des sim w'_def
    by (metis \<open>tw = worldline2 t \<sigma> \<theta> def \<tau>\<close> comp_apply fst_conv snd_conv world_sim_fin.intros
    worldline2_def)
qed

inductive_cases world_sim_fin: "tw, T, cs \<Rightarrow>\<^sub>S tw'"

lemma premises_of_world_sim_fin:
  assumes "tw, T, cs \<Rightarrow>\<^sub>S tw'"
  shows "\<exists>t \<sigma> \<gamma> \<theta> def \<tau> tres. destruct_worldline tw = (t, \<sigma>, \<gamma>, \<theta>, def, \<tau>) \<and> (T, t, \<sigma>, \<gamma>, \<theta>, def \<turnstile> <cs, \<tau>> \<leadsto> tres)
                          \<and> worldline_raw (get_time tres) (get_state tres) (get_beh tres) def (get_trans tres) = snd tw' \<and> fst tw = t \<and> fst tw' = get_time tres"
  using world_sim_fin[OF assms]
  by (smt comp_apply fst_conv fst_destruct_worldline snd_conv)

lemma premises_of_world_sim_fin':
  assumes "tw, T, cs \<Rightarrow>\<^sub>S tw'"
  obtains t \<sigma> \<gamma> \<theta> def \<tau> tres where "destruct_worldline tw = (t, \<sigma>, \<gamma>, \<theta>, def, \<tau>)" and
    "T, t, \<sigma>, \<gamma>, \<theta>, def \<turnstile> <cs, \<tau>> \<leadsto> tres" and   "worldline_raw (get_time tres) (get_state tres) (get_beh tres) def (get_trans tres) = snd tw'"
    and "fst tw = t" and "fst tw' = get_time tres"
  using premises_of_world_sim_fin[OF assms] by auto

lemma world_maxtime_lt_fst_tres:
  assumes "tw, T, cs \<Rightarrow>\<^sub>S tw'"
  shows "T < fst tw'"
proof -
  obtain t \<sigma> \<gamma> \<theta> def \<tau> tres where "destruct_worldline tw = (t, \<sigma>, \<gamma>, \<theta>, def, \<tau>)" and
                              "T, t, \<sigma>, \<gamma>, \<theta>, def \<turnstile> <cs, \<tau>> \<leadsto> tres" and
                              "worldline_raw (get_time tres) (get_state tres) (get_beh tres) def (get_trans tres) = snd tw'"
                          and "fst tw = t" and "fst tw' = get_time tres"
    using premises_of_world_sim_fin'[OF assms] by blast
  thus ?thesis
    using maxtime_lt_fst_tres by metis
qed

definition
sim_hoare_valid :: "'signal assn2 \<Rightarrow> 'signal conc_stmt \<Rightarrow> 'signal assn2 \<Rightarrow> bool" ("\<Turnstile>\<^sub>s \<lbrace>(1_)\<rbrace>/ (_)/ \<lbrace>(1_)\<rbrace>" 50)
where "\<Turnstile>\<^sub>s \<lbrace>P\<rbrace> cs \<lbrace>Q\<rbrace> \<longleftrightarrow> (\<forall>tw T tw'. P tw \<and> (tw, T, cs \<Rightarrow>\<^sub>S tw') \<longrightarrow> Q tw')"

definition worldline_deg :: "'signal worldline \<Rightarrow> nat" where
  "worldline_deg w = (LEAST n. \<forall>t > n. \<forall>s. w s t =  w s n)"

definition world_quiet :: "nat \<times> 'signal worldline_init \<Rightarrow> bool" where
  "world_quiet tw \<longleftrightarrow> fst tw > worldline_deg (wline_of tw)"

definition next_time_world :: "nat \<times> 'signal worldline_init \<Rightarrow> nat" where
  "next_time_world tw =  (let t  = fst tw; w = snd tw;
                              \<tau>  = derivative_raw w t
                          in
                              Femto_VHDL_raw.next_time t \<tau>)"

text \<open>In the definition of @{term "next_time_world"} above, note that after we ``differentiate''
--- perform @{term "derivative_raw"} operation which is a term borrowed from the domain of real
analysis --- the worldline, we need to remove the current transaction at time @{term "t"}. Why?

This is due to the nature of the derivative operation itself. By peeking into its definition,
there will always be a mapping posted at time @{term "t"}. If we do not remove this mapping, the
@{term "next_time"} operation performed next will always return time @{term "t"} --- because
of the @{term "Least"} operator inside the definition of @{term "next_time"} --- and we cannot
advance to the actual next time.\<close>

lemma exist_least_nonzero_sig:
  fixes t :: "nat"
  assumes "\<forall>n. n \<le> t \<longrightarrow> \<tau> n = 0"
  assumes "\<tau> \<noteq> 0"
  shows "\<exists>t' sig val. t < t' \<and> \<tau> t' sig = Some val \<and> (\<forall>n>t. n < t' \<longrightarrow> \<tau> n sig = None)"
proof -
  obtain t' sig where *: " \<tau> t' sig \<noteq> None"
    using assms(2) unfolding zero_fun_def zero_option_def by (metis)
  hence "t' > t"
    using assms(1) by (metis leI option.distinct(1) zero_fun_def zero_option_def)
  hence **: "\<exists>t'>t .  \<tau> t' sig \<noteq> None"
    using * by auto
  define time where "time = (LEAST n. t < n \<and>  \<tau> n sig \<noteq> None)"
  hence " \<tau> time sig \<noteq> None" and "time > t"
    using LeastI_ex[OF **] by auto
  have "\<forall>n > t. n < time \<longrightarrow>  \<tau> n sig = None"
    using not_less_Least time_def by blast
  thus ?thesis
    using ` \<tau> time sig \<noteq> None` `time > t`
    by blast
qed

lemma exist_least_nonzero:
  fixes \<tau> :: "'a trans_raw"
  assumes "\<forall>n\<le>t.  \<tau> n = 0"
  assumes "\<tau> \<noteq> 0"
  shows "\<exists>t'>t.  \<tau> t' \<noteq> 0 \<and> (\<forall>n>t. n < t' \<longrightarrow>  \<tau> n = 0)"
proof -
  obtain t' where *: " \<tau> t' \<noteq> 0"
    using assms(2) unfolding zero_fun_def zero_option_def by (metis)
  hence "t' > t"
    using assms(1)  using leI by auto
  hence **: "\<exists>t'>t.  \<tau> t' \<noteq> 0"
    using * by auto
  define time where "time = (LEAST n. t < n \<and>  \<tau> n \<noteq> 0)"
  hence " \<tau> time \<noteq> 0" and "t < time"
    using LeastI_ex[OF **] by auto
  have "\<forall>n > t. n < time \<longrightarrow>  \<tau> n = 0"
    using not_less_Least time_def by blast
  thus ?thesis
    using ` \<tau> time \<noteq> 0` `time > t` by blast
qed

lemma signal_of_not_default:
  assumes "\<tau> t sig = Some v" and "v \<noteq> def"
  shows "signal_of def \<tau> sig t \<noteq> def"
proof -
  have "Femto_VHDL_raw.inf_time (to_trans_raw_sig \<tau>) sig t = Some t"
  proof (rule inf_time_someI)
    show "t \<in> dom ((to_trans_raw_sig \<tau> sig))"
      using assms(1) by (auto simp add: to_trans_raw_sig_def)
  qed auto
  hence "signal_of def \<tau> sig t = the ((to_trans_raw_sig \<tau> sig) t)"
    unfolding Femto_VHDL_raw.to_signal_def comp_def by auto
  also have "... = v"
    using assms(1) by (auto simp add: to_trans_raw_sig_def)
  finally show ?thesis
    using assms(2) by blast
qed

lemma signal_of_defaultE:
  assumes "signal_of def \<tau> sig t = def"
  shows "\<tau> t sig = None \<or> \<tau> t sig = Some def"
  using assms
proof (rule contrapos_pp)
  assume " \<not> (\<tau> t sig = None \<or> \<tau> t sig = Some def) "
  then obtain v where "\<tau> t sig = Some v" and "v \<noteq> def"
    by auto
  thus "signal_of def \<tau> sig t \<noteq> def"
    by (meson signal_of_not_default)
qed

lemma next_time_world_alt_def1:
  assumes "derivative_raw (snd tw) (fst tw) \<noteq> 0"
  shows "next_time_world tw = (LEAST n. n \<ge> fst tw \<and> (\<lambda>s. wline_of tw s (fst tw)) \<noteq> (\<lambda>s. wline_of tw s n))"
proof -
  define t where "t = fst tw"
  define w where "w = snd tw"
  define \<tau> where "\<tau> = derivative_raw w t"
  have non_stut: "\<forall>s. non_stuttering (to_trans_raw_sig \<tau>) (\<lambda>s. snd w s t) s"
    by (simp add: derivative_raw_ensure_non_stuttering \<tau>_def)
  have "\<tau> \<noteq> 0"
    using assms unfolding \<tau>_def w_def t_def by auto
  hence "next_time_world tw = Femto_VHDL_raw.next_time t \<tau>"
    unfolding next_time_world_def Let_def w_def t_def \<tau>_def by auto
  also have "... = (LEAST n. dom (\<tau> n) \<noteq> {})"
    unfolding Femto_VHDL_raw.next_time_def using `\<tau> \<noteq> 0` by auto
  finally have t'_def: "next_time_world tw = (LEAST n. dom (\<tau> n) \<noteq> {})"
    by auto
  let ?t' = "next_time_world tw"
  have "\<And>n. n \<le> t \<Longrightarrow> \<tau> n = 0"
    unfolding \<tau>_def by (auto simp add: zero_fun_def zero_option_def derivative_raw_def)
  hence "t \<le> ?t'"
    unfolding `next_time_world tw = Femto_VHDL_raw.next_time t \<tau>`  by (simp add: next_time_at_least)
  have "\<exists>x. dom (\<tau> x) \<noteq> {}"
    using `\<tau> \<noteq> 0`
    unfolding zero_fun_def zero_option_def by auto
  hence "dom (\<tau> ?t') \<noteq> {}"
    unfolding `next_time_world tw = (LEAST n. dom (\<tau> n) \<noteq> {})` by (rule LeastI_ex)
  hence "\<tau> ?t' \<noteq> Map.empty"
    by simp
  then obtain sig val where "\<tau> ?t' sig = Some val"
    by (meson not_Some_eq)
  hence non_stut_sig: "non_stuttering (to_trans_raw_sig \<tau>) (\<lambda>s. snd w s t) sig"
    using non_stut by auto
  have "(\<lambda>s. snd w s t) \<noteq> (\<lambda>s. snd w s (next_time_world tw))"
  proof
    let ?\<sigma> = "\<lambda>s. snd w s t"
    assume " (\<lambda>s. snd w s t) = (\<lambda>s. snd w s (next_time_world tw))"
    hence "snd w sig t = snd w sig (next_time_world tw)"
      by metis
    moreover have helper1: "snd w sig t = signal_of (?\<sigma> sig) \<tau> sig t"
      by (metis \<open>\<And>n. n \<le> t \<Longrightarrow> \<tau> n = 0\<close> signal_of_def zero_fun_def)
    moreover have " signal_of (?\<sigma> sig)  \<tau> sig ?t' = snd w sig ?t'"
      by (unfold \<tau>_def, intro signal_of_derivative_raw)(simp add: \<open>t \<le> next_time_world tw\<close>)+
    ultimately have "signal_of (?\<sigma> sig) \<tau> sig t = signal_of (?\<sigma> sig) \<tau> sig ?t'"
      by auto
    have "t < ?t'"
    proof (rule ccontr)
      assume "\<not> t < ?t'" hence "?t' \<le> t" by auto
      hence "\<tau> ?t' = 0"
        using `\<And>n. n \<le> t \<Longrightarrow> \<tau> n = 0` by auto
      with `\<tau> ?t' sig = Some val` show False
        by (simp add: zero_fun_def zero_option_def)
    qed
    have "t < ?t' - 1 \<Longrightarrow> signal_of (?\<sigma> sig) \<tau> sig (?t' - 1) = signal_of (?\<sigma> sig) \<tau> sig t"
    proof (rule signal_of_less_ind)
      have "\<forall>n. t < n \<and> n < ?t' \<longrightarrow> \<tau> n = 0"
        using t'_def \<open>next_time_world tw = Femto_VHDL_raw.next_time t \<tau>\<close> next_time_at_least2 by auto
      thus "\<And>n. t < n \<Longrightarrow> n \<le> next_time_world tw - 1 \<Longrightarrow> \<tau> n = 0"
        by auto
    qed auto
    with `t < ?t'` have "signal_of (?\<sigma> sig) \<tau> sig (?t' - 1) = signal_of (?\<sigma> sig) \<tau> sig t"
      by (metis \<tau>_def helper1 linorder_neqE_nat signal_of2_derivative_before_now)
    hence "signal_of (?\<sigma> sig) \<tau> sig (?t' - 1) = signal_of (?\<sigma> sig) \<tau> sig ?t'"
      using \<open>signal_of (snd w sig t) \<tau> sig t = signal_of (snd w sig t) \<tau> sig (next_time_world tw)\<close>
      by simp
    hence "\<tau> ?t' sig = None"
      using \<open>t < next_time_world tw\<close> current_sig_and_prev_same non_stut_sig zero_option_def
      by (metis gr0I gr_implies_not0)
    with `\<tau> ?t' sig = Some val` show False by auto
  qed
  have "(LEAST n. n \<ge> t \<and> (\<lambda>s. snd w s t) \<noteq> (\<lambda>s. snd w s n)) = next_time_world tw"
  proof (rule Least_equality)
    show "t \<le> next_time_world tw \<and> (\<lambda>s. snd w s t) \<noteq> (\<lambda>s. snd w s (next_time_world tw))"
      by (simp add: \<open>(\<lambda>s. snd w s t) \<noteq> (\<lambda>s.  snd w s (next_time_world tw))\<close> \<open>t \<le> next_time_world tw\<close>)
  next
    { fix y
      let ?\<sigma> = "\<lambda>s. snd w s t"
      assume "\<not> ?t' \<le> y" hence "y < ?t'" by auto
      have "y < t \<or> \<not> y < t" by auto
      moreover
      { assume "\<not> y < t" hence "t \<le> y" by auto
        have "\<And>n. t < n \<Longrightarrow> n \<le> y \<Longrightarrow> \<tau> n = 0"
          using `y < ?t'` t'_def
          by (metis \<open>next_time_world tw = Femto_VHDL_raw.next_time t \<tau>\<close> le_less_trans  next_time_at_least2)
        have "\<And>s.  snd w s t = signal_of (?\<sigma> s) \<tau> s t"
          using `\<And>n. n \<le> t \<Longrightarrow> \<tau> n = 0`
          by (metis signal_of_less_ind signal_of_zero zero_fun_def zero_le)
        moreover have "\<And>s. signal_of (?\<sigma> s) \<tau> s y =  snd w s y"
          by (unfold \<tau>_def, intro signal_of_derivative_raw)(simp add: \<open>t \<le> y\<close>)+
        moreover have "\<And>s. signal_of (?\<sigma> s) \<tau> s y = signal_of (?\<sigma> s) \<tau> s t"
        proof (cases "t < y")
          case True
          thus "\<And>s. signal_of (?\<sigma> s) \<tau> s y = signal_of (?\<sigma> s) \<tau> s t"
            by (meson \<open>\<And>n. \<lbrakk>t < n; n \<le> y\<rbrakk> \<Longrightarrow> \<tau> n = 0\<close> \<open>t \<le> y\<close> signal_of_less_ind)
        next
          case False
          with `t \<le> y` show "\<And>s. signal_of (?\<sigma> s) \<tau> s y = signal_of (?\<sigma> s) \<tau> s t"
            by auto
        qed
        ultimately have "(\<lambda>s. snd w s t) = (\<lambda>s. snd w s y)"
          by auto
        hence "\<not> (t \<le> y \<and> (\<lambda>s.  snd w s t) \<noteq> (\<lambda>s.  snd w s y))"
          by auto }
      moreover
      { assume "y < t"
        hence "\<not> (t \<le> y \<and> (\<lambda>s.  snd w s t) \<noteq> (\<lambda>s.  snd w s y))"
          by auto }
      ultimately have "\<not> (t \<le> y \<and> (\<lambda>s.  snd w s t) \<noteq> (\<lambda>s.  snd w s y))"
        by auto }
    thus "\<And>y. t \<le> y \<and> (\<lambda>s. snd w s t) \<noteq> (\<lambda>s. snd w s y) \<Longrightarrow> ?t' \<le> y"
      by auto
  qed
  thus ?thesis
    unfolding w_def t_def by auto
qed

lemma next_time_world_alt_def2:
  assumes "derivative_raw (snd tw) (fst tw) = 0"
  shows "next_time_world tw = fst tw + 1"
  using assms  by (simp add: next_time_world_def)

lemma derivative_raw_alt_def:
  "derivative_raw (snd tw) (fst tw) \<noteq> 0 \<longleftrightarrow>  (\<exists>n\<ge> (fst tw). (\<lambda>s. (wline_of tw) s (fst tw)) \<noteq> (\<lambda>s. (wline_of tw) s n))"
proof
  assume "derivative_raw (snd tw) (fst tw) \<noteq> 0"
  hence *: "\<exists>n. derivative_raw (snd tw) (fst tw) n \<noteq> Map.empty"
    unfolding zero_option_def zero_fun_def by auto
  define least where "least = (LEAST n. derivative_raw (snd tw) (fst tw) n \<noteq> Map.empty)"
  have "derivative_raw (snd tw) (fst tw) least \<noteq> Map.empty"
    using LeastI_ex[OF *] unfolding least_def by auto
  then obtain s val where "derivative_raw (snd tw) (fst tw) least s = Some val"
    unfolding zero_fun_def zero_option_def  by fastforce
  hence "fst tw < least"
    unfolding derivative_raw_def  using not_le by fastforce
  hence "difference_raw (snd tw) least s = Some val"
    using \<open>derivative_raw (snd tw) (fst tw) least s = Some val\<close> unfolding derivative_raw_def by auto
  hence "wline_of tw s least \<noteq> wline_of tw s (least - 1)"
    using `fst tw < least` unfolding difference_raw_def by force
  have **: "\<forall>n<least. derivative_raw (snd tw) (fst tw) n = Map.empty"
    unfolding least_def using not_less_Least by blast
  have "\<forall>n. fst tw < n \<and> n < least \<longrightarrow> wline_of tw s n = wline_of tw s (fst tw)"
  proof (intro allI, intro impI)
    fix n
    assume "fst tw < n \<and> n < least"
    hence "derivative_raw (snd tw) (fst tw) n = Map.empty" and "fst tw < n" and "n < least"
      using ** by auto
    have "signal_of (wline_of tw s (fst tw)) (derivative_raw (snd tw) (fst tw)) s n = (wline_of tw) s n"
      by (metis \<open>get_time tw < n\<close> comp_apply less_imp_le_nat signal_of_derivative_raw state_of_world_def)
    hence "(wline_of tw) s n = signal_of (wline_of tw s (fst tw)) (derivative_raw (snd tw) (fst tw)) s n"
      by auto
    also have "... = signal_of (wline_of tw s (fst tw)) (derivative_raw (snd tw) (fst tw)) s (fst tw)"
      by(intro signal_of_less_ind')
        (simp add: \<open>fst tw < n \<and> n < least\<close> ** le_less_trans zero_option_def order.strict_implies_order)+
    also have "... = (wline_of tw) s (fst tw)"
      by (metis derivative_raw_def signal_of_def zero_option_def)
    finally show "wline_of tw s n = wline_of tw s (fst tw)"
      by auto
  qed
  hence "wline_of tw s (least - 1) = wline_of tw s (fst tw)"
    using `fst tw < least`
    by (metis (no_types, lifting) Suc_diff_1 diff_less less_SucE less_Suc_eq_0_disj
    less_imp_Suc_add zero_less_one)
  hence "wline_of tw s least \<noteq> wline_of tw s (fst tw)"
    using `wline_of tw s least \<noteq> wline_of tw s (least - 1)` by auto
  with `fst tw < least` show "\<exists>n\<ge>fst tw. (\<lambda>s. wline_of tw s (fst tw)) \<noteq> (\<lambda>s. wline_of tw s n)"
    by (metis (full_types) less_imp_le_nat)
next
  assume *: "\<exists>n\<ge>fst tw. (\<lambda>s. wline_of tw s (fst tw)) \<noteq> (\<lambda>s. wline_of tw s n)"
  define least where "least = (LEAST n. n \<ge> fst tw \<and> (\<lambda>s. wline_of tw s (fst tw)) \<noteq> (\<lambda>s. wline_of tw s n))"
  hence "fst tw \<le> least" and **: "(\<lambda>s. wline_of tw s (fst tw)) \<noteq> (\<lambda>s. wline_of tw s least)"
    using LeastI_ex[OF *] unfolding least_def by auto
  hence "fst tw < least"
    using nat_less_le by blast
  have "\<forall>n. fst tw < n \<and> n < least \<longrightarrow> (\<forall>s. wline_of tw s (fst tw) = wline_of tw s n)"
    unfolding least_def  by (metis (mono_tags, lifting) Least_le leD le_eq_less_or_eq)
  hence "(\<lambda>s. wline_of tw s (fst tw)) = (\<lambda>s. wline_of tw s (least - 1))"
    using `fst tw < least`
    by (metis (no_types, hide_lams) add.commute add_cancel_right_right diff_Suc_1 diff_less
    gr0_conv_Suc less_antisym less_diff_conv not_add_less2 not_less_iff_gr_or_eq zero_less_one)
  hence "(\<lambda>s. wline_of tw s least) \<noteq> (\<lambda>s. wline_of tw s (least - 1))"
    using ** by auto
  have "difference_raw (snd tw) least \<noteq> 0"
  proof (rule ccontr)
    assume "\<not> difference_raw (snd tw) least \<noteq> 0" hence "difference_raw (snd tw) least = 0"
      by auto
    hence "(\<lambda>s. if wline_of tw s least \<noteq> wline_of tw s (least - 1) then Some (wline_of tw s least) else None) = 0"
      using `fst tw < least` unfolding difference_raw_def
      by (metis comp_apply gr_implies_not_zero)
    hence "(\<lambda>s. wline_of tw s least) = (\<lambda>s. wline_of tw s (least - 1))"
      by (intro ext)(smt option.distinct(1) zero_fun_def zero_option_def)
    with `(\<lambda>s. wline_of tw s least) \<noteq> (\<lambda>s. wline_of tw s (least - 1))` show False
      by auto
  qed
  hence "derivative_raw (snd tw) (fst tw) least \<noteq> 0"
    using `fst tw < least` unfolding derivative_raw_def by auto
  thus "derivative_raw (snd tw) (fst tw) \<noteq> 0"
    by (metis zero_fun_def)
qed

lemma next_time_world_alt_def:
  "next_time_world tw = (let t =fst tw; w = wline_of tw in
                            if \<exists>n\<ge>t. (\<lambda>s. w s t) \<noteq> (\<lambda>s. w s n) then (LEAST n. n \<ge> t \<and> (\<lambda>s. w s t) \<noteq> (\<lambda>s. w s n))
                            else t + 1)"
proof -
  have "derivative_raw (snd tw) (fst tw) = 0 \<or> derivative_raw (snd tw) (fst tw) \<noteq> 0"
    by auto
  moreover
  { assume "derivative_raw (snd tw) (fst tw) \<noteq> 0"
    hence "(\<exists>n\<ge> (fst tw). (\<lambda>s. (wline_of tw) s (fst tw)) \<noteq> (\<lambda>s. (wline_of tw) s n))"
      unfolding derivative_raw_alt_def by auto
    hence ?thesis
      using next_time_world_alt_def1[OF `derivative_raw (snd tw) (fst tw) \<noteq> 0`]
      unfolding Let_def by auto }
  moreover
  { assume "derivative_raw (snd tw) (fst tw) = 0"
    hence "\<not> (\<exists>n\<ge> (fst tw). (\<lambda>s. (wline_of tw) s (fst tw)) \<noteq> (\<lambda>s. (wline_of tw) s n))"
      using derivative_raw_alt_def by blast
    hence ?thesis
      using next_time_world_alt_def2[OF `derivative_raw (snd tw) (fst tw) = 0`]
      unfolding Let_def by auto }
  ultimately show ?thesis
    by auto
qed

lemma next_time_world_at_least:
  "fst tw < next_time_world tw"
proof -
  have "\<exists>n\<ge>get_time tw. (\<lambda>s. wline_of tw s (get_time tw)) \<noteq> (\<lambda>s. wline_of tw s n) \<or>
       \<not> (\<exists>n\<ge>get_time tw. (\<lambda>s. wline_of tw s (get_time tw)) \<noteq> (\<lambda>s. wline_of tw s n))"
    by auto
  moreover
  { assume "\<not> (\<exists>n\<ge>get_time tw. (\<lambda>s. wline_of tw s (get_time tw)) \<noteq> (\<lambda>s. wline_of tw s n))"
    hence "next_time_world tw = get_time tw + 1"
      unfolding next_time_world_alt_def Let_def by auto
    hence "fst tw < next_time_world tw"
      by auto }
  moreover
  { assume *: "\<exists>n\<ge>get_time tw. (\<lambda>s. wline_of tw s (get_time tw)) \<noteq> (\<lambda>s. wline_of tw s n)"
    hence "next_time_world tw = (LEAST n. get_time tw \<le> n \<and> (\<lambda>s. wline_of tw s (get_time tw)) \<noteq> (\<lambda>s. wline_of tw s n))"
      unfolding next_time_world_alt_def Let_def by auto
    hence "get_time tw < next_time_world tw"
      using LeastI_ex[OF *] by auto
    hence "fst tw < next_time_world tw"
      by auto }
  ultimately show ?thesis by auto
qed

lemma unchanged_until_next_time_world:
  "\<forall>i\<ge>fst tw. i < next_time_world tw \<longrightarrow> (\<forall>s. wline_of tw s i = wline_of tw s (fst tw))"
proof (rule allI, rule impI, rule impI)
  fix i
  assume "fst tw \<le> i"
  assume "i < next_time_world tw"
  have "   \<exists>n\<ge>get_time tw. (\<lambda>s. wline_of tw s (get_time tw)) \<noteq> (\<lambda>s. wline_of tw s n) \<or>
        \<not> (\<exists>n\<ge>get_time tw. (\<lambda>s. wline_of tw s (get_time tw)) \<noteq> (\<lambda>s. wline_of tw s n))"
    by auto
  moreover
  { assume "\<exists>n\<ge>get_time tw. (\<lambda>s. wline_of tw s (get_time tw)) \<noteq> (\<lambda>s. wline_of tw s n)"
    hence "next_time_world tw = (LEAST n. get_time tw \<le> n \<and> (\<lambda>s. wline_of tw s (get_time tw)) \<noteq> (\<lambda>s. wline_of tw s n))"
      unfolding next_time_world_alt_def Let_def by auto
    hence "i < (LEAST n. fst tw  \<le> n \<and> (\<lambda>s. wline_of tw s (get_time tw)) \<noteq> (\<lambda>s. wline_of tw s n))"
      using \<open>i < next_time_world tw\<close> by auto
    hence "\<not> (get_time tw \<le> i \<and> (\<lambda>s. wline_of tw s (get_time tw)) \<noteq> (\<lambda>s. wline_of tw s i))"
      using not_less_Least by auto
    with \<open>fst tw \<le> i\<close> have "\<forall>s. wline_of tw s i = wline_of tw s (fst tw)"
      by metis }
  moreover
  { assume "\<not> (\<exists>n\<ge>get_time tw. (\<lambda>s. wline_of tw s (get_time tw)) \<noteq> (\<lambda>s. wline_of tw s n))"
    hence "\<forall>n\<ge>fst tw. \<forall>s. wline_of tw s n = wline_of tw s (fst tw)"
      by metis
    hence "\<forall>s. wline_of tw s i = wline_of tw s (fst tw)"
      using \<open>fst tw \<le> i\<close>  by blast }
  ultimately show "\<forall>s. wline_of tw s i = wline_of tw s (fst tw)"
    by auto
qed

lemma successive_empty_event:
  assumes "event_of tw = {}" and "event_of (next_time_world tw, snd tw) = {}"
  shows "next_time_world tw = fst tw + 1"
proof (rule ccontr)
  assume "next_time_world tw \<noteq> fst tw + 1"
  hence "fst tw + 1 < next_time_world tw"
    using next_time_world_at_least by (metis discrete less_le)
  hence *: "\<exists>n\<ge>fst tw. (\<lambda>s. wline_of tw s (fst tw)) \<noteq> (\<lambda>s. wline_of tw s n)" and
        "next_time_world tw = (LEAST n. get_time tw \<le> n \<and> (\<lambda>s. wline_of tw s (get_time tw)) \<noteq> (\<lambda>s. wline_of tw s n))"
    unfolding next_time_world_alt_def Let_def  by presburger+
  hence "(\<lambda>s. wline_of tw s (get_time tw)) \<noteq> (\<lambda>s. wline_of tw s (next_time_world tw))"
    using LeastI_ex[OF *]  by simp
  hence **: "\<exists>s. wline_of tw s (next_time_world tw) \<noteq> wline_of tw s (fst tw)"
    by auto
  have "\<And>s. wline_of tw s (next_time_world tw) = wline_of tw s (next_time_world tw - 1)"
    using assms(2) unfolding event_of_alt_def
    using \<open>get_time tw + 1 < next_time_world tw\<close> by auto
  thus False
    by (metis "**" One_nat_def \<open>get_time tw + 1 < next_time_world tw\<close> add_le_imp_le_diff
    diff_Suc_less gr0I gr_implies_not_zero nat_less_le unchanged_until_next_time_world)
qed

inductive
  conc_sim :: "'signal assn2 \<Rightarrow> 'signal conc_stmt \<Rightarrow> 'signal assn2 \<Rightarrow> bool"
  ("\<turnstile>\<^sub>s (\<lbrace>(1_)\<rbrace>/ (_)/ \<lbrace>(1_)\<rbrace>)" 50)
  where
While: "\<turnstile> \<lbrace>\<lambda>tw. P tw\<rbrace> cs \<lbrace> \<lambda>tw. P (next_time_world tw, snd tw)\<rbrace>  \<Longrightarrow> \<turnstile>\<^sub>s \<lbrace>P\<rbrace> cs \<lbrace>P\<rbrace>" |
Conseq_sim: "\<forall>tw. P' tw \<longrightarrow> P tw \<Longrightarrow> \<turnstile>\<^sub>s \<lbrace>P\<rbrace> cs \<lbrace>Q\<rbrace> \<Longrightarrow> \<forall>tw. Q tw \<longrightarrow> Q' tw \<Longrightarrow> \<turnstile>\<^sub>s \<lbrace>P'\<rbrace> cs \<lbrace>Q'\<rbrace>"

lemma worldline_next_config:
  assumes "context_invariant t \<sigma> \<gamma> \<theta> def \<tau>'"
  shows "worldline_raw t \<sigma> \<theta> def \<tau>' = worldline_raw (next_time t \<tau>') (next_state t \<tau>' \<sigma>) (add_to_beh \<sigma> \<theta> t (next_time t \<tau>')) def \<tau>'"
proof (rule, rule_tac[2] ext, rule_tac[2] ext)
  fix s' t'
  have "t' < t \<or> t \<le> t' \<and> t' < next_time t \<tau>' \<or> next_time t \<tau>' \<le> t'"
    by auto
  moreover
  { assume "t' < t"
    hence "t' < next_time t \<tau>'"
      using next_time_at_least assms unfolding context_invariant_def
      by (metis le_less_trans nat_less_le)
    have "\<And>n. n \<le> t' \<Longrightarrow>  \<theta> n =  (add_to_beh \<sigma> \<theta> t (next_time t \<tau>')) n"
      using `t' < t` unfolding add_to_beh_def
      by (cases "t < next_time t \<tau>'", auto)
    hence "signal_of (def s') \<theta> s' t' = signal_of (def s') (add_to_beh \<sigma> \<theta> t (next_time t \<tau>')) s' t'"
      by (metis eq_imp_le signal_of_equal_when_trans_equal_upto)
    hence "snd (worldline_raw t \<sigma> \<theta> def \<tau>') s' t' = snd (worldline_raw (next_time t \<tau>') (next_state t \<tau>' \<sigma>) (add_to_beh \<sigma> \<theta> t (next_time t \<tau>')) def \<tau>') s' t'"
      unfolding worldline_raw_def using `t' < t` `t' < next_time t \<tau>'` by auto }
  moreover
  { assume "next_time t \<tau>' \<le> t'"
    moreover have "t \<le> next_time t \<tau>'"
      using assms unfolding context_invariant_def by (simp add: next_time_at_least)
    ultimately have "t \<le> t'"
      by auto
    have "signal_of (\<sigma> s') \<tau>' s' t' =  signal_of (next_state t \<tau>' \<sigma> s') \<tau>' s' t'"
    proof (cases "inf_time (to_trans_raw_sig \<tau>') s' t' = None")
      case True
      hence " \<forall>t\<in>dom ( (to_trans_raw_sig \<tau>' s')). t' < t"
        by (simp add: inf_time_none_iff)
      hence "\<forall>t. t \<le> t' \<longrightarrow> t \<notin> dom (  (to_trans_raw_sig \<tau>' s'))"
        using not_le by blast
      hence "next_time t \<tau>' \<notin> dom (  (to_trans_raw_sig \<tau>' s'))"
        using `next_time t \<tau>' \<le> t'` by auto
      hence "s' \<notin> dom (\<tau>' (next_time t \<tau>'))"
        unfolding next_time_def by (auto simp add: to_trans_raw_sig_def)
      hence "next_state t \<tau>' \<sigma> s' = \<sigma> s'"
        unfolding next_state_def Let_def by auto
      then show ?thesis
        using True unfolding to_signal_def comp_def by auto
    next
      case False
      then show ?thesis
        unfolding to_signal_def comp_def by auto
    qed
    hence "snd (worldline_raw t \<sigma> \<theta> def \<tau>') s' t' =
         snd (worldline_raw (next_time t \<tau>') (next_state t \<tau>' \<sigma>) (add_to_beh \<sigma> \<theta> t (next_time t \<tau>')) def \<tau>') s' t'"
      unfolding worldline_raw_def using `t \<le> t'` and `next_time t \<tau>' \<le> t'` by auto }
  moreover
  { assume "t \<le> t' \<and> t' < next_time t \<tau>'"
    hence "t < next_time t \<tau>'"
      by auto
    have add_to_beh: "add_to_beh \<sigma> \<theta> t (next_time t \<tau>') = \<theta>(t := (Some o \<sigma>))"
      unfolding add_to_beh_def using `t < next_time t \<tau>'` by auto
    have "signal_of (\<sigma> s') \<tau>' s' t' = \<sigma> s'"
    proof -
      have "\<forall>n<next_time t \<tau>'.  \<tau>' n = 0"
        using `t < next_time t \<tau>'` next_time_at_least2 by auto
      hence "\<forall>n. n \<le> t' \<longrightarrow>  \<tau>' n = 0"
        using `t \<le> t' \<and> t' < next_time t \<tau>'` by auto
      have "\<forall>t\<in>dom ( (to_trans_raw_sig \<tau>' s')). t' < t"
      proof (rule ccontr)
        assume "\<not> (\<forall>t\<in>dom ( (to_trans_raw_sig \<tau>' s')). t' < t)"
        then obtain time where "time \<in> dom ( (to_trans_raw_sig \<tau>' s'))" and "time \<le> t'"
          using leI by blast
        hence " \<tau>' time \<noteq> 0"
          by (transfer', auto simp add: to_trans_raw_sig_def zero_fun_def zero_fun_def zero_option_def zero_option_def)
        moreover have " \<tau>' time = 0"
          using `\<forall>n. n \<le> t' \<longrightarrow>  \<tau>' n = 0` `time \<le> t'` by auto
        ultimately show False by auto
      qed
      hence "inf_time (to_trans_raw_sig \<tau>') s' t' = None"
        by (auto simp add: inf_time_none_iff)
      thus ?thesis
        unfolding to_signal_def comp_def by auto
    qed
    moreover have "signal_of (def s') (\<theta>(t :=Some o \<sigma>)) s' t' = \<sigma> s'"
    proof -
      have "\<forall>n<next_time t \<tau>'.  \<tau>' n = 0"
        using next_time_at_least2 `t < next_time t \<tau>'` by auto
      hence "\<forall>n. n \<le> t' \<longrightarrow>  \<tau>' n = 0"
        using `t \<le> t' \<and> t' < next_time t \<tau>'` by auto
      have "t \<in> dom ( (to_trans_raw_sig (\<theta>(t :=Some o \<sigma>)) s'))"
        by transfer' (auto simp add: to_trans_raw_sig_def)
      moreover have "t \<le> t'"
        using `t \<le> t' \<and> t' < next_time t \<tau>'` by auto
      moreover have "\<forall>ta\<in>dom ( (to_trans_raw_sig(\<theta>(t :=Some o \<sigma>)) s')). ta \<le> t' \<longrightarrow> ta \<le> t"
      proof (rule ccontr)
        assume "\<not> (\<forall>ta\<in>dom ( (to_trans_raw_sig (\<theta>(t :=Some o \<sigma>)) s')). ta \<le> t' \<longrightarrow> ta \<le> t)"
        then obtain ta where ta_dom: "ta\<in>dom ( (to_trans_raw_sig (\<theta>(t :=Some o \<sigma>)) s'))"  and  "ta \<le> t'" and "ta > t"
          using leI by blast
        have " (to_trans_raw_sig (\<theta>(t :=Some o \<sigma>)) s') ta =   (to_trans_raw_sig \<theta> s') ta"
          using `ta > t` by  (auto simp add: to_trans_raw_sig_def)
        hence " \<theta> ta \<noteq> 0"
          using ta_dom by ( auto simp add: to_trans_raw_sig_def zero_fun_def zero_fun_def zero_option_def zero_option_def)
        have "\<forall>n \<ge> t.  \<theta> n = 0"
          using assms(1) unfolding context_invariant_def by auto
        hence " \<theta> ta = 0"
          using `ta > t` by auto
        with ` \<theta> ta \<noteq> 0` show False by auto
      qed
      ultimately have "inf_time (to_trans_raw_sig (\<theta>(t :=Some o \<sigma>))) s' t' = Some t"
        by (rule inf_time_someI)
      moreover have "the ( (to_trans_raw_sig (\<theta>(t :=Some o \<sigma>)) s') t) = \<sigma> s'"
        by (auto simp add: to_trans_raw_sig_def)
      ultimately show ?thesis
        unfolding to_signal_def comp_def by auto
    qed
    ultimately have "signal_of (\<sigma> s') \<tau>' s' t' = signal_of (def s') (\<theta>(t :=Some o \<sigma>)) s' t'"
      by auto
    hence "signal_of (\<sigma> s') \<tau>' s' t' = signal_of (def s') (add_to_beh \<sigma> \<theta> t (next_time t \<tau>')) s' t'"
      unfolding add_to_beh by auto
    hence "snd (worldline_raw t \<sigma> \<theta> def \<tau>') s' t' = snd (worldline_raw (next_time t \<tau>') (next_state t \<tau>' \<sigma>) (add_to_beh \<sigma> \<theta> t (next_time t \<tau>')) def \<tau>') s' t'"
      unfolding worldline_raw_def using `t \<le> t' \<and> t' < next_time t \<tau>'` by auto }
  ultimately show "snd (worldline_raw t \<sigma> \<theta> def \<tau>') s' t' = snd (worldline_raw (next_time t \<tau>') (next_state t \<tau>' \<sigma>) (add_to_beh \<sigma> \<theta> t (next_time t \<tau>')) def \<tau>') s' t'"
    by auto
qed (simp add: worldline_raw_def)

lemma worldline_next_config_next_time:
  assumes "context_invariant t \<sigma> \<gamma> \<theta> def \<tau>'"
  shows "worldline_raw t \<sigma> \<theta> def \<tau>' = worldline_raw (next_time t \<tau>') (next_state t \<tau>' \<sigma>) (add_to_beh \<sigma> \<theta> t (next_time t \<tau>')) def (\<tau>'(next_time t \<tau>' := 0))"
proof (rule, rule_tac[2] ext, rule_tac[2] ext)
  fix s' t'
  have "t' < t \<or> t \<le> t' \<and> t' < next_time t \<tau>' \<or> next_time t \<tau>' \<le> t'"
    by auto
  moreover
  { assume "t' < t"
    hence "t' < next_time t \<tau>'"
      using next_time_at_least assms unfolding context_invariant_def
      by (metis (no_types, lifting) dual_order.trans less_imp_le_nat not_less)
    have "\<And>n. n \<le> t' \<Longrightarrow>  \<theta> n =  (add_to_beh \<sigma> \<theta> t (next_time t \<tau>')) n"
      using `t' < t` unfolding add_to_beh_def
      by (cases "t < next_time t \<tau>'") (auto)
    hence "signal_of (def s') \<theta> s' t' = signal_of (def s') (add_to_beh \<sigma> \<theta> t (next_time t \<tau>')) s' t'"
      by (metis order_refl signal_of_equal_when_trans_equal_upto)
    hence "snd (worldline_raw t \<sigma> \<theta> def \<tau>') s' t' = snd (worldline_raw (next_time t \<tau>') (next_state t \<tau>' \<sigma>) (add_to_beh \<sigma> \<theta> t (next_time t \<tau>')) def (\<tau>'(next_time t \<tau>' := 0))) s' t'"
      unfolding worldline_raw_def using `t' < t` `t' < next_time t \<tau>'` by auto }
  moreover
  { assume "next_time t \<tau>' \<le> t'"
    moreover have "t \<le> next_time t \<tau>'"
      using assms unfolding context_invariant_def
      by (simp add: next_time_at_least)
    ultimately have "t \<le> t'"
      by auto
    have "signal_of (\<sigma> s') \<tau>' s' t' =  signal_of (next_state t \<tau>' \<sigma> s') (\<tau>'(next_time t \<tau>' := 0)) s' t'"
    proof (cases "inf_time (to_trans_raw_sig \<tau>') s' t' = None")
      case True
      hence " \<forall>t\<in>dom ( (to_trans_raw_sig \<tau>' s')). t' < t"
        by (auto simp add: inf_time_none_iff)
      hence "\<forall>t. t \<le> t' \<longrightarrow> t \<notin> dom (  (to_trans_raw_sig \<tau>' s'))"
        using not_le by blast
      hence "next_time t \<tau>' \<notin> dom (  (to_trans_raw_sig \<tau>' s'))"
        using `next_time t \<tau>' \<le> t'` by auto
      hence "s' \<notin> dom ( \<tau>' (next_time t \<tau>'))"
        unfolding next_time_def by (auto simp add: to_trans_raw_sig_def)
      hence "next_state t \<tau>' \<sigma> s' = \<sigma> s'"
        unfolding next_state_def Let_def by auto
      moreover have "inf_time (to_trans_raw_sig (\<tau>'(next_time t \<tau>' := 0))) s' t' =
            inf_time (to_trans_raw_sig \<tau>') s' t'"
        using True by (metis inf_time_rem_curr_trans option.distinct(1) rem_curr_trans_to_trans_raw_sig)
      ultimately show ?thesis
        using True unfolding to_signal_def comp_def by auto
    next
      case False
      then obtain time where "inf_time (to_trans_raw_sig \<tau>') s' t' = Some time"
        by auto
      have "time = next_time t \<tau>' \<or> time \<noteq> next_time t \<tau>'"
        by auto
      moreover
      { assume "time \<noteq> next_time t \<tau>'"
        hence "inf_time (to_trans_raw_sig (\<tau>'(next_time t \<tau>' := 0))) s' t' =  inf_time (to_trans_raw_sig \<tau>') s' t'"
          using `inf_time (to_trans_raw_sig \<tau>') s' t' = Some time`
          by (metis inf_time_rem_curr_trans option.inject rem_curr_trans_to_trans_raw_sig)
        hence ?thesis
          using `inf_time (to_trans_raw_sig \<tau>') s' t' = Some time` `time \<noteq> next_time t \<tau>'`
          unfolding to_signal_def comp_def
          by (metis False option.case_eq_if option.sel rem_curr_trans_to_trans_raw_sig
          trans_value_same_except_at_removed) }
      moreover
      { assume "time = next_time t \<tau>'"
        hence "inf_time (to_trans_raw_sig \<tau>') s' t' = Some (next_time t \<tau>')"
          using `inf_time (to_trans_raw_sig \<tau>') s' t' = Some time` by auto
        hence *: "signal_of (\<sigma> s') \<tau>' s' t' = the ( (to_trans_raw_sig \<tau>' s') (next_time t \<tau>'))"
          unfolding to_signal_def comp_def by auto
        have "next_time t \<tau>' \<in> dom ( (to_trans_raw_sig \<tau>' s'))"
          by (metis (full_types) \<open>inf_time (to_trans_raw_sig \<tau>') s' t' = Some time\<close> \<open>time =
          next_time t \<tau>'\<close> dom_def inf_time_some_exists keys_def zero_option_def)
        hence "s' \<in> dom ( \<tau>' (next_time t \<tau>'))"
          unfolding next_time_def by (auto simp add: to_trans_raw_sig_def)
        moreover have "the ( (to_trans_raw_sig \<tau>' s') (next_time t \<tau>')) = the ( \<tau>' (next_time t \<tau>') s')"
          unfolding next_time_def by (auto simp add: to_trans_raw_sig_def)
        ultimately have "the ( (to_trans_raw_sig \<tau>' s') (next_time t \<tau>')) = next_state t \<tau>' \<sigma> s'"
          unfolding next_state_def Let_def by auto
        with * have "signal_of (\<sigma> s') \<tau>' s' t' = next_state t \<tau>' \<sigma> s'"
          by auto
        have "\<And>n. n < next_time t \<tau>' \<Longrightarrow>  \<tau>' n = 0"
          using next_time_at_least2 by auto
        hence "inf_time (to_trans_raw_sig (\<tau>'(next_time t \<tau>' := 0))) s' t' = None"
          using inf_time_rem_curr_trans_at_t[OF `inf_time (to_trans_raw_sig \<tau>') s' t' = Some (next_time t \<tau>')`]
          by (metis rem_curr_trans_to_trans_raw_sig to_trans_raw_sig_def zero_fun_def zero_option_def)
        hence ?thesis
          unfolding `signal_of (\<sigma> s') \<tau>' s' t' = next_state t \<tau>' \<sigma> s'` to_signal_def by auto }
      ultimately show ?thesis
        unfolding to_signal_def comp_def by auto
    qed
    hence "snd (worldline_raw t \<sigma> \<theta> def \<tau>') s' t' =
           snd (worldline_raw (next_time t \<tau>') (next_state t \<tau>' \<sigma>) (add_to_beh \<sigma> \<theta> t (next_time t \<tau>')) def (\<tau>'(next_time t \<tau>' := 0))) s' t'"
      unfolding worldline_raw_def using `t \<le> t'` and `next_time t \<tau>' \<le> t'` by auto }
  moreover
  { assume "t \<le> t' \<and> t' < next_time t \<tau>'"
    hence "t < next_time t \<tau>'"
      by auto
    have add_to_beh: "add_to_beh \<sigma> \<theta> t (next_time t \<tau>') = \<theta>(t :=Some o \<sigma>)"
      unfolding add_to_beh_def using `t < next_time t \<tau>'` by auto
    have "signal_of (\<sigma> s') \<tau>' s' t' = \<sigma> s'"
    proof -
      have "\<forall>n<next_time t \<tau>'.  \<tau>' n = 0"
        using `t < next_time t \<tau>'` next_time_at_least2 by auto
      hence "\<forall>n. n \<le> t' \<longrightarrow>  \<tau>' n = 0"
        using `t \<le> t' \<and> t' < next_time t \<tau>'` by auto
      have "\<forall>t\<in>dom ( (to_trans_raw_sig \<tau>' s')). t' < t"
      proof (rule ccontr)
        assume "\<not> (\<forall>t\<in>dom ( (to_trans_raw_sig \<tau>' s')). t' < t)"
        then obtain time where "time \<in> dom ( (to_trans_raw_sig \<tau>' s'))" and "time \<le> t'"
          using leI by blast
        hence " \<tau>' time \<noteq> 0"
          by (auto simp add: to_trans_raw_sig_def zero_fun_def zero_fun_def zero_option_def zero_option_def)
        moreover have " \<tau>' time = 0"
          using `\<forall>n. n \<le> t' \<longrightarrow>  \<tau>' n = 0` `time \<le> t'` by auto
        ultimately show False by auto
      qed
      hence "inf_time (to_trans_raw_sig \<tau>') s' t' = None"
        by (simp add: inf_time_none_iff)
      thus ?thesis
        unfolding to_signal_def comp_def by auto
    qed
    moreover have "signal_of (def s') (\<theta>(t := Some o \<sigma>)) s' t' = \<sigma> s'"
    proof -
      have "\<forall>n<next_time t \<tau>'.  \<tau>' n = 0"
        using next_time_at_least2 `t < next_time t \<tau>'` by auto
      hence "\<forall>n. n \<le> t' \<longrightarrow>  \<tau>' n = 0"
        using `t \<le> t' \<and> t' < next_time t \<tau>'` by auto
      have "t \<in> dom ( (to_trans_raw_sig (\<theta>(t := Some o \<sigma>)) s'))"
        by  (auto simp add: to_trans_raw_sig_def)
      moreover have "t \<le> t'"
        using `t \<le> t' \<and> t' < next_time t \<tau>'` by auto
      moreover have "\<forall>ta\<in>dom ( (to_trans_raw_sig (\<theta>(t := Some o \<sigma>)) s')). ta \<le> t' \<longrightarrow> ta \<le> t"
      proof (rule ccontr)
        assume "\<not> (\<forall>ta\<in>dom ( (to_trans_raw_sig (\<theta>(t := Some o \<sigma>)) s')). ta \<le> t' \<longrightarrow> ta \<le> t)"
        then obtain ta where ta_dom: "ta\<in>dom ( (to_trans_raw_sig (\<theta>(t := Some o \<sigma>)) s'))"  and  "ta \<le> t'" and "ta > t"
          using leI by blast
        have " (to_trans_raw_sig (\<theta>(t := Some o \<sigma>)) s') ta =   (to_trans_raw_sig \<theta> s') ta"
          using `ta > t` by  (auto simp add: to_trans_raw_sig_def)
        hence " \<theta> ta \<noteq> 0"
          using ta_dom by (auto simp add: to_trans_raw_sig_def zero_fun_def zero_fun_def zero_option_def zero_option_def)
        have "\<forall>n \<ge> t.  \<theta> n = 0"
          using assms(1) unfolding context_invariant_def by auto
        hence " \<theta> ta = 0"
          using `ta > t` by auto
        with ` \<theta> ta \<noteq> 0` show False by auto
      qed
      ultimately have "inf_time (to_trans_raw_sig (\<theta>(t := Some o \<sigma>))) s' t' = Some t"
        by (rule inf_time_someI)
      moreover have "the ( (to_trans_raw_sig (\<theta>(t := Some o \<sigma>)) s') t) = \<sigma> s'"
        by  (auto simp add: to_trans_raw_sig_def)
      ultimately show ?thesis
        unfolding to_signal_def comp_def by auto
    qed
    ultimately have "signal_of (\<sigma> s') \<tau>' s' t' = signal_of (def s') (\<theta>(t := Some o \<sigma>)) s' t'"
      by auto
    hence "signal_of (\<sigma> s') \<tau>' s' t' = signal_of (def s') (add_to_beh \<sigma> \<theta> t (next_time t \<tau>')) s' t'"
      unfolding add_to_beh by auto
    hence "snd (worldline_raw t \<sigma> \<theta> def \<tau>') s' t' =
           snd (worldline_raw (next_time t \<tau>') (next_state t \<tau>' \<sigma>) (add_to_beh \<sigma> \<theta> t (next_time t \<tau>')) def (\<tau>'(next_time t \<tau>' := 0))) s' t'"
      unfolding worldline_raw_def using `t \<le> t' \<and> t' < next_time t \<tau>'` by auto }
  ultimately show "snd (worldline_raw t \<sigma> \<theta> def \<tau>') s' t' =
                   snd (worldline_raw (next_time t \<tau>') (next_state t \<tau>' \<sigma>) (add_to_beh \<sigma> \<theta> t (next_time t \<tau>')) def (\<tau>'(next_time t \<tau>' := 0))) s' t'"
    by auto
qed (simp add: worldline_raw_def)

lemma worldline2_next_config:
  assumes "context_invariant t \<sigma> \<gamma> \<theta> def \<tau>'"
  shows "(next_time t \<tau>', snd (worldline2 t \<sigma> \<theta> def \<tau>')) = worldline2 (next_time t \<tau>') (next_state t \<tau>' \<sigma>) (add_to_beh \<sigma> \<theta> t (next_time t \<tau>')) def \<tau>'"
proof -
  have "worldline_raw t \<sigma> \<theta> def \<tau>' = worldline_raw (next_time t \<tau>') (next_state t \<tau>' \<sigma>) (add_to_beh \<sigma> \<theta> t (next_time t \<tau>')) def \<tau>'"
    using worldline_next_config assms by metis
  thus ?thesis
    unfolding worldline2_def by auto
qed

lemma worldline2_next_config_next_time:
  assumes "context_invariant t \<sigma> \<gamma> \<theta> def \<tau>'"
  shows "(next_time t \<tau>', snd (worldline2 t \<sigma> \<theta> def \<tau>')) = worldline2 (next_time t \<tau>') (next_state t \<tau>' \<sigma>) (add_to_beh \<sigma> \<theta> t (next_time t \<tau>')) def (\<tau>'(next_time t \<tau>' := 0))"
proof -
  have "worldline_raw t \<sigma> \<theta> def \<tau>' = worldline_raw (next_time t \<tau>') (next_state t \<tau>' \<sigma>) (add_to_beh \<sigma> \<theta> t (next_time t \<tau>')) def (\<tau>'(next_time t \<tau>' := 0))"
    using worldline_next_config_next_time using assms by metis
  thus ?thesis
    unfolding worldline2_def by auto
qed

lemma non_stuttering_preserved:
  assumes "non_stuttering (to_trans_raw_sig \<tau>) \<sigma> s"
  shows   "non_stuttering (to_trans_raw_sig (\<tau>(next_time t \<tau> := 0))) (next_state t \<tau> \<sigma>) s"
proof -
  define ks where "ks = keys (to_trans_raw_sig \<tau> s)"
  define ks_del where "ks_del = keys (to_trans_raw_sig (\<tau>(next_time t \<tau> := 0)) s)"
  { fix k1 k2 :: nat
    assume "k1 < k2"
    assume "k1 \<in> ks_del" and "k2 \<in> ks_del"
    assume "\<forall>k. k1 < k \<and> k < k2 \<longrightarrow> k \<notin> ks_del"
    have "k1 \<in> ks" and "k2 \<in> ks"
      using `k1 \<in> ks_del` `k2 \<in> ks_del` unfolding ks_del_def ks_def to_trans_raw_sig_def keys_def
      by (metis (mono_tags) fun_upd_apply mem_Collect_eq zero_fun_def)+
    have "next_time t \<tau> < k1"
      using `k1 \<in> ks_del` unfolding ks_del_def to_trans_raw_sig_def keys_def
      by (metis domIff dom_def fun_upd_apply nat_neq_iff next_time_at_least2 zero_fun_def zero_option_def)
    hence "\<forall>k. k1 < k \<and> k < k2 \<longrightarrow> k \<notin> ks"
      using `\<forall>k. k1 < k \<and> k < k2 \<longrightarrow> k \<notin> ks_del` unfolding ks_del_def ks_def to_trans_raw_sig_def
      keys_def by auto
    with `k1 \<in> ks` and `k2 \<in> ks` have "to_trans_raw_sig \<tau> s k1 \<noteq> to_trans_raw_sig  \<tau> s k2"
      using assms `k1 < k2` unfolding non_stuttering_def ks_def by auto
    moreover have "to_trans_raw_sig \<tau> s k1 = to_trans_raw_sig (\<tau>(next_time t \<tau> := 0)) s k1"
      using `next_time t \<tau> < k1` unfolding to_trans_raw_sig_def by auto
    moreover have "to_trans_raw_sig \<tau> s k2 = to_trans_raw_sig (\<tau>(next_time t \<tau> := 0)) s k2"
      using `next_time t \<tau> < k1` `k1 < k2` unfolding to_trans_raw_sig_def by auto
    ultimately have "to_trans_raw_sig (\<tau>(next_time t \<tau> := 0)) s k1 \<noteq>
                                            to_trans_raw_sig (\<tau>(next_time t \<tau> := 0)) s k2"
      by auto }
  note first_po = this
  { assume "ks_del \<noteq> {}"
    hence "\<tau> \<noteq> 0" and "\<tau>(next_time t \<tau> := 0) \<noteq> 0"
      unfolding ks_del_def to_trans_raw_sig_def keys_def
      by (metis (mono_tags, lifting) Collect_empty_eq fun_upd_idem zero_fun_def)+
    define least_del where "least_del \<equiv> (LEAST k. k \<in> keys (to_trans_raw_sig (\<tau>(next_time t \<tau> := 0)) s))"
    have "least_del \<in> keys (to_trans_raw_sig (\<tau>(next_time t \<tau> := 0)) s)"
      using LeastI_ex `ks_del \<noteq> {}` unfolding ks_del_def
      by (metis (full_types) Collect_mem_eq empty_Collect_eq least_del_def)
    hence "dom ((\<tau>(next_time t \<tau> := 0)) least_del) \<noteq> {}"
      by (metis domIff dom_def empty_iff keys_def to_trans_raw_sig_def zero_option_def)
    have "next_time t \<tau> \<le> least_del"
    proof (rule ccontr)
      assume "\<not> next_time t \<tau> \<le> least_del"
      hence "least_del < next_time t \<tau>" by auto
      hence "least_del < (LEAST n. dom (\<tau> n) \<noteq> {})"
        unfolding next_time_def using `\<tau> \<noteq> 0` by auto
      with not_less_Least have "dom (\<tau> least_del) = {}"
        by auto
      moreover have "dom (\<tau> least_del) \<noteq> {}"
        using `dom ((\<tau>(next_time t \<tau> := 0)) least_del) \<noteq> {}` `least_del < next_time t \<tau>`
        by simp
      ultimately show False by auto
    qed
    moreover  have "next_time t \<tau> \<noteq> least_del"
      by (metis \<open>dom ((\<tau>(next_time t \<tau> := 0)) least_del) \<noteq> {}\<close> dom_eq_empty_conv fun_upd_same
      zero_fun_def zero_option_def)
    ultimately have "next_time t \<tau> < least_del"
      using `next_time t \<tau> \<le> least_del` by auto
    have "next_time t \<tau> \<in> ks \<or> next_time t \<tau> \<notin> ks"
      by auto
    have "least_del \<in> ks"
      using `next_time t \<tau> < least_del` `least_del \<in> keys (to_trans_raw_sig (\<tau>(next_time t \<tau> := 0)) s)`
      unfolding ks_def by (simp add: keys_def to_trans_raw_sig_def)
    moreover have "\<forall>k. next_time t \<tau> < k \<and> k < least_del \<longrightarrow> k \<notin> ks"
    proof (rule, rule)
      fix k
      assume "next_time t \<tau> < k \<and> k < least_del"
      hence "next_time t \<tau> < k" and "k < least_del"
        by auto
      hence "k \<notin> ks_del"
        unfolding ks_del_def least_del_def using not_less_Least by blast
      thus "k \<notin> ks"
        using `next_time t \<tau> < k` unfolding ks_del_def ks_def keys_def
        by (simp add: to_trans_raw_sig_def)
    qed
    moreover
    { assume "next_time t \<tau> \<in> ks"
      hence "s \<in> dom (\<tau> (next_time t \<tau>))"
        unfolding ks_def keys_def to_trans_raw_sig_def  by (simp add: dom_def zero_option_def)
      hence *: "next_state t \<tau> \<sigma> s = the (to_trans_raw_sig \<tau> s (next_time t \<tau>))"
        unfolding next_state_def Let_def to_trans_raw_sig_def by auto
      have "to_trans_raw_sig \<tau> s (next_time t \<tau>) \<noteq> to_trans_raw_sig \<tau> s least_del"
        using `next_time t \<tau> \<in> ks` `next_time t \<tau> < least_del` assms unfolding non_stuttering_def
        ks_def  using calculation(1) calculation(2) ks_def by blast
      moreover have "to_trans_raw_sig \<tau> s least_del = to_trans_raw_sig (\<tau>(next_time t \<tau> := 0)) s least_del"
        using `next_time t \<tau> \<noteq> least_del`  by (metis fun_upd_apply to_trans_raw_sig_def)
      ultimately have "to_trans_raw_sig \<tau> s (next_time t \<tau>) \<noteq> to_trans_raw_sig (\<tau>(next_time t \<tau> := 0)) s least_del"
        by auto
      hence " next_state t \<tau> \<sigma> s \<noteq>
        the (to_trans_raw_sig (\<tau>(next_time t \<tau> := 0)) s (LEAST k. k \<in> keys (to_trans_raw_sig (\<tau>(next_time t \<tau> := 0)) s)))"
        using * unfolding least_del_def
      proof -
        assume a1: "to_trans_raw_sig \<tau> s (next_time t \<tau>) \<noteq> to_trans_raw_sig (\<tau>(next_time t \<tau> := 0)) s (LEAST k. k \<in> keys (to_trans_raw_sig (\<tau>(next_time t \<tau> := 0)) s))"
          have "{n. to_trans_raw_sig \<tau> s n \<noteq> 0} = ks"
        by (simp add: keys_def ks_def)
        then have f2: "\<And>n. n \<notin> ks \<or> to_trans_raw_sig \<tau> s n \<noteq> None"
        using zero_option_def by force
        then have "to_trans_raw_sig \<tau> s least_del \<noteq> None"
        using \<open>least_del \<in> ks\<close> by blast
        then show ?thesis
          using f2 a1 \<open>next_state t \<tau> \<sigma> s = the (to_trans_raw_sig \<tau> s (next_time t \<tau>))\<close> \<open>next_time t \<tau> \<in> ks\<close> \<open>to_trans_raw_sig \<tau> s least_del = to_trans_raw_sig (\<tau>(next_time t \<tau> := 0)) s least_del\<close> least_del_def by force
      qed }
    moreover
    { assume "next_time t \<tau> \<notin> ks"
      hence "s \<notin> dom (\<tau> (next_time t \<tau>))"
        unfolding ks_def to_trans_raw_sig_def keys_def by (auto simp add: zero_option_def)
      hence "next_state t \<tau> \<sigma> s = \<sigma> s"
        unfolding next_state_def Let_def by auto
      have "to_trans_raw_sig \<tau> s least_del = to_trans_raw_sig (\<tau>(next_time t \<tau> := 0)) s least_del"
        using `next_time t \<tau> \<noteq> least_del`  by (metis fun_upd_apply to_trans_raw_sig_def)
      have "to_trans_raw_sig (\<tau>(next_time t \<tau> := 0)) s = to_trans_raw_sig \<tau> s"
        using `s \<notin> dom (\<tau> (next_time t \<tau>))` unfolding to_trans_raw_sig_def
        by (intro ext)(simp add: domIff zero_fun_def zero_option_def)
      hence "least_del = (LEAST k. k \<in> keys (to_trans_raw_sig \<tau> s))" (is "_ = ?least")
        unfolding least_del_def by auto
      have "ks \<noteq> {}"
        using `ks_del \<noteq> {}` `next_time t \<tau> \<notin> ks` unfolding ks_del_def ks_def
        by (simp add: \<open>to_trans_raw_sig (\<tau>(next_time t \<tau> := 0)) s = to_trans_raw_sig \<tau> s\<close>)
      have "\<sigma> s \<noteq> the (to_trans_raw_sig \<tau> s ?least)"
        using assms unfolding non_stuttering_def using \<open>ks \<noteq> {}\<close> ks_def by blast
      hence " next_state t \<tau> \<sigma> s \<noteq>
        the (to_trans_raw_sig (\<tau>(next_time t \<tau> := 0)) s (LEAST k. k \<in> keys (to_trans_raw_sig (\<tau>(next_time t \<tau> := 0)) s)))"
        by (simp add: \<open>next_state t \<tau> \<sigma> s = \<sigma> s\<close> \<open>to_trans_raw_sig (\<tau>(next_time t \<tau> := 0)) s = to_trans_raw_sig \<tau> s\<close>) }
    ultimately have "next_state t \<tau> \<sigma> s \<noteq>
        the (to_trans_raw_sig (\<tau>(next_time t \<tau> := 0)) s (LEAST k. k \<in> keys (to_trans_raw_sig (\<tau>(next_time t \<tau> := 0)) s)))"
      by auto }
  with first_po show ?thesis
    unfolding non_stuttering_def ks_del_def by auto
qed

lemma b_seq_exec_mono_wrt_history:
  assumes "t, \<sigma>, \<gamma>, \<theta>,  def \<turnstile> <cs, \<tau>> \<longrightarrow>\<^sub>s \<tau>'"
  assumes "\<And>k s. signal_of (def s) \<theta> s k = signal_of (def s) \<theta>' s k"
  shows   "t, \<sigma>, \<gamma>, \<theta>', def \<turnstile> <cs, \<tau>> \<longrightarrow>\<^sub>s \<tau>'"
  using assms
  by (induction rule:b_seq_exec.inducts)(meson b_seq_exec.intros beval_cong)+

lemma b_conc_exec_mono_wrt_history:
  assumes "t, \<sigma>, \<gamma>, \<theta>,  def \<turnstile> <cs, \<tau>> \<longrightarrow>\<^sub>c \<tau>'"
  assumes "\<And>k s. signal_of (def s) \<theta> s k = signal_of (def s) \<theta>' s k"
  shows   "t, \<sigma>, \<gamma>, \<theta>', def \<turnstile> <cs, \<tau>> \<longrightarrow>\<^sub>c \<tau>'"
  using assms
  by (induction rule:b_conc_exec.inducts)(meson b_conc_exec.intros beval_cong b_seq_exec_mono_wrt_history)+

lemma while_soundness2:
  assumes "\<Turnstile> \<lbrace>\<lambda>tw. P tw \<rbrace> cs \<lbrace>\<lambda>tw. P (next_time_world tw, snd tw)\<rbrace>"
  assumes "tw, T, cs \<Rightarrow>\<^sub>S tw'"
  assumes "P tw"
  assumes "nonneg_delay_conc cs" and "conc_stmt_wf cs"
  shows   "P tw'"
proof -
  obtain t \<sigma> \<gamma> \<theta> \<tau> def res where des: "destruct_worldline tw = (t, \<sigma>, \<gamma>, \<theta>, def, \<tau>)" and
  sim: "T, t, \<sigma>, \<gamma>, \<theta>, def \<turnstile> <cs, \<tau>> \<leadsto> res" and   woh: "tw' = (get_time res, worldline_raw (get_time res) (get_state res) (get_beh res) def (get_trans res))"
    using premises_of_world_sim_fin'[OF assms(2)]
    by (smt prod.exhaust_sel)
  have tau_def:  "\<tau> = derivative_raw (snd tw) (fst tw)" and
      sigma_def: "\<sigma> = (\<lambda>s. wline_of tw s (fst tw))" and
      theta_def: "\<theta> = derivative_hist_raw (snd tw) (fst tw)" and
      gamma_def: "\<gamma> = {s. wline_of tw s (fst tw) \<noteq> signal_of (def s) (derivative_hist_raw (snd tw) (fst tw)) s (fst tw - 1)}"
    using des unfolding destruct_worldline_def Let_def by auto
  have non_stut: "\<forall>s. non_stuttering (to_trans_raw_sig \<tau>) \<sigma> s"
    unfolding tau_def sigma_def   by (simp add: derivative_raw_ensure_non_stuttering)
  have non_stut2: "\<forall>s. non_stuttering (to_trans_raw_sig \<theta>) def s"
    using des destruct_worldline_ensure_non_stuttering_hist_raw theta_def by blast
  have "tw = worldline2 t \<sigma> \<theta> def \<tau>" and "context_invariant t \<sigma> \<gamma> \<theta> def \<tau>"
    using worldline2_constructible[OF des] by auto
  (*TODO : try to enter the non_stut2 into the inductive hypothesis *)
  with sim show ?thesis
    using woh assms(1) assms(3-5) non_stut gamma_def
  proof (induction arbitrary: tw rule:b_simulate_fin.induct)
    case (1 t maxtime \<tau> \<gamma> \<sigma> \<theta> def cs \<tau>' res)
    hence "\<And>n. n \<le> t \<Longrightarrow> \<tau> n = 0"
      unfolding context_invariant_def by auto
    have "snd tw = worldline_raw t \<sigma> \<theta> def \<tau>"
      using 1(5-6) unfolding worldline2_def by auto
    obtain theta where dw_def: "destruct_worldline tw = (t, \<sigma>, \<gamma>, theta, def, \<tau>)" and
                    "\<And>k s. signal_of (def s) \<theta> s k = signal_of (def s) theta s k"
      using destruct_worldline_correctness4[OF \<open>context_invariant t \<sigma> \<gamma> \<theta> def \<tau>\<close> \<open>\<forall>s. non_stuttering
      (to_trans_raw_sig \<tau>) \<sigma> s\<close>]  using "1.prems"(1) by blast
    hence "b_conc_exec t \<sigma> \<gamma> theta def cs \<tau> \<tau>'"
      using b_conc_exec_mono_wrt_history[OF \<open> t , \<sigma> , \<gamma> , \<theta>, def  \<turnstile> <cs , \<tau>> \<longrightarrow>\<^sub>c \<tau>'\<close>]
      by blast
    then obtain tw_conc where "tw, cs \<Rightarrow>\<^sub>c tw_conc" and "worldline2 t \<sigma> theta def \<tau>' = tw_conc"
      using \<open>destruct_worldline tw = (t, \<sigma>, \<gamma>, theta, def, \<tau>)\<close>
      using world_conc_exec.intros by blast
    with `P tw`  have "P (next_time_world tw_conc, snd tw_conc)"
      using 1(9) unfolding conc_hoare_valid_def by presburger
    have "fst tw = fst tw_conc"
      using fst_world_conc_exec `tw, cs \<Rightarrow>\<^sub>c tw_conc` by metis
    have "world_conc_exec tw cs tw_conc"
      using world_conc_exec_rem_curr_trans_eq_only_if[OF 1(11-12)] `tw, cs \<Rightarrow>\<^sub>c tw_conc` by auto
    have " \<tau> t = 0"
      by (auto simp add: `\<And>n. n \<le> t \<Longrightarrow> \<tau> n = 0`)
    hence "t < next_time t \<tau>'"
      using  nonneg_delay_conc_next_time_strict[OF _ `t , \<sigma> , \<gamma> , \<theta>, def \<turnstile> <cs , \<tau>> \<longrightarrow>\<^sub>c \<tau>'` `nonneg_delay_conc cs` `conc_stmt_wf cs`]
      \<open>\<And>n. n \<le> t \<Longrightarrow> \<tau> n = 0\<close> dual_order.order_iff_strict  by blast
    have ci: "context_invariant (next_time t \<tau>') (next_state t \<tau>' \<sigma>) (next_event t \<tau>' \<sigma>) (add_to_beh \<sigma> \<theta> t (next_time t \<tau>')) def (\<tau>'(next_time t \<tau>' := 0))"
      using context_invariant[OF 1(7) 1(3) `t < next_time t \<tau>'`]  by auto
    have "context_invariant t \<sigma> \<gamma> theta def \<tau>"
      using worldline2_constructible using dw_def by blast
    have "worldline2 t \<sigma> \<theta> def \<tau>' = tw_conc"
      unfolding sym[OF `worldline2 t \<sigma> theta def \<tau>' = tw_conc`] worldline2_def worldline_raw_def
      `\<And>k s. signal_of (def s) \<theta> s k = signal_of (def s) theta s k` by auto
    hence "fst tw_conc = t"
      by auto
    have "snd tw_conc = worldline_raw t \<sigma> \<theta> def \<tau>'"
      using `worldline2 t \<sigma> \<theta> def \<tau>' = tw_conc` unfolding worldline2_def by auto
    have "context_invariant t \<sigma> \<gamma> \<theta> def \<tau>'"
      using b_conc_exec_preserves_context_invariant[OF 1(3) `context_invariant t \<sigma> \<gamma> \<theta> def \<tau>` `nonneg_delay_conc cs`]
      by auto
    hence "\<And>n. n \<le> t \<Longrightarrow> \<tau>' n = 0"
      unfolding context_invariant_def by auto
    have "\<forall>s. non_stuttering (to_trans_raw_sig \<tau>') \<sigma> s"
      by (meson "1.prems"(6) "1.prems"(7) "1.prems"(8) \<open>\<And>n. n \<le> t \<Longrightarrow> \<tau> n = 0\<close> \<open>t , \<sigma> , \<gamma> , theta, def
      \<turnstile> <cs , \<tau>> \<longrightarrow>\<^sub>c \<tau>'\<close> b_conc_exec_preserves_non_stuttering)
    have "next_time_world tw_conc = next_time t \<tau>'"
      unfolding next_time_world_def Let_def `snd tw_conc = worldline_raw t \<sigma> \<theta> def \<tau>'`
      using derivative_raw_of_worldline `context_invariant t \<sigma> \<gamma> \<theta> def \<tau>'` `\<forall>s. non_stuttering (to_trans_raw_sig \<tau>') \<sigma> s`
      unfolding world_quiet_def worldline_deg_def `fst tw = fst tw_conc` `snd tw_conc = worldline_raw t \<sigma> \<theta> def \<tau>'`
      context_invariant_def
      by (simp add: derivative_raw_of_worldline_specific \<open>fst tw_conc = t\<close>)
    hence twc: "(next_time_world tw_conc, snd tw_conc) =
             worldline2 (next_time t \<tau>') (next_state t \<tau>' \<sigma>) (add_to_beh \<sigma> \<theta> t (next_time t \<tau>')) def (\<tau>'(next_time t \<tau>' := 0))"
      using `worldline2 t \<sigma> \<theta> def \<tau>' = tw_conc` worldline2_next_config_next_time[OF `context_invariant t \<sigma> \<gamma> \<theta> def \<tau>'`]
      by auto
    have ns: " \<forall>s. non_stuttering (to_trans_raw_sig (\<tau>'(next_time t \<tau>' := 0))) (next_state t \<tau>' \<sigma>) s"
      using non_stuttering_preserved `context_invariant t \<sigma> \<gamma> \<theta> def \<tau>'` unfolding context_invariant_def
      by (simp add: non_stuttering_preserved \<open>\<forall>s. non_stuttering (to_trans_raw_sig \<tau>') \<sigma> s\<close>)
    have ne: "next_event t \<tau>' \<sigma> = {s. (wline_of (next_time_world tw_conc, snd tw_conc)) s (fst (next_time_world tw_conc, snd tw_conc)) \<noteq>
      signal_of (def s) (derivative_hist_raw ( (snd (next_time_world tw_conc, snd tw_conc))) (fst (next_time_world tw_conc, snd tw_conc))) s
       (fst (next_time_world tw_conc, snd tw_conc) - 1)}" (is "_ = ?complex")
    proof -
      have "?complex = {s.  (wline_of tw_conc) s (next_time_world tw_conc) \<noteq>
      signal_of (def s) (derivative_hist_raw ( (snd tw_conc)) (next_time_world tw_conc)) s
       (next_time_world tw_conc - 1)}"
        by auto
      also have "... = {s. snd (worldline_raw t \<sigma> \<theta> def \<tau>') s (next_time t \<tau>') \<noteq>
                           signal_of (def s) (derivative_hist_raw (worldline_raw t \<sigma> \<theta> def \<tau>') (next_time t \<tau>')) s (next_time t \<tau>' - 1)}"
        using ` (snd tw_conc) = worldline_raw t \<sigma> \<theta> def \<tau>'` `next_time_world tw_conc = next_time t \<tau>'`
        by auto
      also have "... = {s. snd (worldline_raw t \<sigma> \<theta> def \<tau>') s (next_time t \<tau>') \<noteq>  signal_of (def s) (add_to_beh \<sigma> \<theta> t (next_time t \<tau>')) s (next_time t \<tau>' - 1)}"
      proof -
        have 0: "snd (worldline2 t \<sigma> \<theta> def \<tau>') = worldline_raw t \<sigma> \<theta> def \<tau>'"
          by (auto simp add: worldline2_def)
        have *: "... = worldline_raw (next_time t \<tau>') (next_state t \<tau>' \<sigma>) (add_to_beh \<sigma> \<theta> t (next_time t \<tau>')) def (\<tau>'(next_time t \<tau>' := 0)) "
          using worldline_next_config_next_time[OF `context_invariant t \<sigma> \<gamma> \<theta> def \<tau>'`] by auto
        have **: "snd (worldline2 (next_time t \<tau>') (next_state t \<tau>' \<sigma>) (add_to_beh \<sigma> \<theta> t (next_time t \<tau>')) def (\<tau>' (next_time t \<tau>' := 0))) =
              worldline_raw (next_time t \<tau>') (next_state t \<tau>' \<sigma>) (add_to_beh \<sigma> \<theta> t (next_time t \<tau>')) def (\<tau>'(next_time t \<tau>' := 0))"
          unfolding worldline2_def by auto
        have "\<And>s. signal_of (def s) (derivative_hist_raw (worldline_raw t \<sigma> \<theta> def \<tau>') (next_time t \<tau>')) s (next_time t \<tau>' - 1) =
                   signal_of (def s) (add_to_beh \<sigma> \<theta> t (next_time t \<tau>')) s (next_time t \<tau>' - 1)"
          using hist_of_worldline ci unfolding context_invariant_def ** sym[OF *]
          by (smt "*" "**")
        thus ?thesis
          by auto
      qed
      also have "... = {s. next_state t \<tau>' \<sigma> s \<noteq> signal_of (def s) (add_to_beh \<sigma> \<theta> t (next_time t \<tau>')) s (next_time t \<tau>' - 1)}"
      proof -
        have "t \<le> next_time t \<tau>'"
          using next_time_at_least[OF `\<And>n. n \<le> t \<Longrightarrow> \<tau>' n = 0`] by auto
        hence "\<And>s. snd (worldline_raw t \<sigma> \<theta> def \<tau>') s (next_time t \<tau>') = signal_of (\<sigma> s) \<tau>' s (next_time t \<tau>')"
          unfolding worldline_raw_def by auto
        moreover have "\<And>s. signal_of (\<sigma> s) \<tau>' s (next_time t \<tau>') = next_state t \<tau>' \<sigma> s"
        proof -
          fix s
          have "s \<in> (dom ( \<tau>' (next_time t \<tau>'))) \<or> s \<notin> (dom ( \<tau>' (next_time t \<tau>')))"
            by auto
          moreover
          { assume s_dom: "s \<in> dom ( \<tau>' (next_time t \<tau>'))"
            then obtain val where lookup: " \<tau>' (next_time t \<tau>') s = Some val"
              by auto
            hence "next_state t \<tau>' \<sigma> s = val"
              unfolding next_state_def Let_def using s_dom by auto
            also have "... = signal_of (\<sigma> s) \<tau>' s (next_time t \<tau>')"
              using lookup trans_some_signal_of' by fastforce
            finally have "signal_of (\<sigma> s) \<tau>' s (next_time t \<tau>') = next_state t \<tau>' \<sigma> s"
              by auto }
          moreover
          { have " \<tau> t s = 0"
              using ` \<tau> t  = 0` by (auto simp add: zero_fun_def zero_option_def zero_option_def)
            have "\<And>n. n < t \<Longrightarrow>  \<tau>' n  = 0"
              using `context_invariant t \<sigma> \<gamma> \<theta> def \<tau>'` unfolding context_invariant_def by auto
            assume s_not_dom: "s \<notin> dom ( \<tau>' (next_time t \<tau>'))"
            hence "next_state t \<tau>' \<sigma> s = \<sigma> s"
              unfolding next_state_def Let_def by auto
            have "\<And>n. n < t \<Longrightarrow>  \<tau>' n s = 0"
              using s_not_dom \<open>\<And>n. n < t \<Longrightarrow>  \<tau>' n = 0\<close>  by (simp add: zero_fun_def)
            have "\<And>n. t < n \<Longrightarrow> n < next_time t \<tau>' \<Longrightarrow>  \<tau>' n = 0"
              by (simp add: until_next_time_zero)
            hence "\<And>n. t < n \<Longrightarrow> n \<le> next_time t \<tau>' \<Longrightarrow>  \<tau>' n s = 0"
              using s_not_dom by (metis (full_types) domIff nat_less_le zero_fun_def zero_fun_def zero_option_def)
            hence "signal_of (\<sigma> s) \<tau>' s (next_time t \<tau>') = signal_of (\<sigma> s) \<tau>' s t"
              by (metis \<open>t \<le> next_time t \<tau>'\<close> le_neq_implies_less signal_of_less_ind')
            also have "... = signal_of (\<sigma> s) \<tau>' s 0"
              by (meson \<open>\<And>n. n \<le> t \<Longrightarrow> \<tau>' n = 0\<close> less_eq_nat.simps(1) signal_of_less_ind)
            also have "... = \<sigma> s"
              by (metis \<open>\<tau> t = 0\<close> \<open>\<tau> t s = 0\<close> domIff le0 le_neq_implies_less
              next_time_at_least2 s_not_dom signal_of_zero zero_fun_def zero_option_def)
            finally have "signal_of (\<sigma> s) \<tau>' s (next_time t \<tau>') = \<sigma> s"
              by auto
            hence "signal_of (\<sigma> s) \<tau>' s (next_time t \<tau>') = next_state t \<tau>' \<sigma> s"
              using \<open>next_state t \<tau>' \<sigma> s = \<sigma> s\<close> by simp }
          ultimately show " signal_of (\<sigma> s) \<tau>' s (next_time t \<tau>') = next_state t \<tau>' \<sigma> s"
            by auto
        qed
        ultimately have "\<And>s. snd (worldline_raw t \<sigma> \<theta> def \<tau>') s (next_time t \<tau>') = next_state t \<tau>' \<sigma> s"
          by auto
        thus ?thesis by auto
      qed
      also have "... = {s. next_state t \<tau>' \<sigma> s \<noteq> \<sigma> s}"
      proof -
        have "t \<le> next_time t \<tau>'"
          using \<open>\<And>n. n \<le> t \<Longrightarrow>  \<tau>' n = 0\<close> next_time_at_least  by (simp add: next_time_at_least)
        moreover have "\<And>n. t \<le> n \<Longrightarrow>  \<theta> n = 0"
          using `context_invariant t \<sigma> \<gamma> \<theta> def \<tau>` unfolding context_invariant_def by auto
        ultimately have "\<And>s n. t < n \<Longrightarrow> n \<le> next_time t \<tau>' - 1 \<Longrightarrow> (add_to_beh \<sigma> \<theta> t (next_time t \<tau>')) n s = 0"
          unfolding add_to_beh_def by (simp add: lookup_update zero_fun_def)
        hence "t \<le> next_time t \<tau>' - 1"
          using `t < next_time t \<tau>'` by auto
        { fix s
          have "signal_of (def s) (add_to_beh \<sigma> \<theta> t (next_time t \<tau>')) s (next_time t \<tau>' - 1) =
                signal_of (def s) (add_to_beh \<sigma> \<theta> t (next_time t \<tau>')) s t"
            using `t \<le> next_time t \<tau>' - 1`
            by (metis (full_types) \<open>\<And>s n. \<lbrakk>t < n; n \<le> next_time t \<tau>' - 1\<rbrakk> \<Longrightarrow> (add_to_beh \<sigma> \<theta> t (next_time t \<tau>')) n s = 0\<close> le_neq_implies_less signal_of_less_ind')
          also have "... =  signal_of (def s) (\<theta>(t:= Some o \<sigma>)) s t"
            using `t < next_time t \<tau>'` unfolding add_to_beh_def by auto
          also have "... = \<sigma> s"
            by (meson fun_upd_same trans_some_signal_of)
          finally have "signal_of (def s) (add_to_beh \<sigma> \<theta> t (next_time t \<tau>')) s (next_time t \<tau>' - 1) = \<sigma> s"
            by auto }
        hence "\<And>s. signal_of (def s) (add_to_beh \<sigma> \<theta> t (next_time t \<tau>')) s (next_time t \<tau>' - 1) = \<sigma> s"
          by auto
        thus ?thesis by auto
      qed
      also have "... = next_event t \<tau>' \<sigma>"
        unfolding next_event_alt_def by auto
      finally show ?thesis by auto
    qed
    show ?case
      using 1(5)[OF twc ci 1(8-9) _ 1(11-12) ns ne] `P (next_time_world tw_conc, snd tw_conc)`
      by auto
  next
    case (2 t maxtime \<tau> \<gamma> \<sigma> \<theta> def cs)
    hence "\<forall>n. t \<le> n \<longrightarrow>  \<theta> n = 0"
      unfolding context_invariant_def by auto
    have "worldline2 t \<sigma> \<theta> def \<tau> = (t, def, worldline_of_history def (\<theta>(t := Some \<circ> \<sigma>)))"
    proof
      show "get_time (worldline2 t \<sigma> \<theta> def \<tau>) = get_time (t, def, worldline_of_history def (\<theta>(t := Some \<circ> \<sigma>)))"
        by simp
    next
      have "worldline_raw t \<sigma> \<theta> def \<tau> = (def, \<lambda>s' t'. signal_of (def s') (\<theta>(t := Some \<circ> \<sigma>)) s' t')"
      proof (rule, rule_tac[2] ext, rule_tac[2] ext)
        fix s' t'
        have "t' < t \<or> t \<le> t'" by auto
        moreover
        { assume "t' < t"
          hence *: "\<And>n. n < t \<Longrightarrow>  (to_trans_raw_sig  (\<theta>(t := Some \<circ> \<sigma>)) s') n = (to_trans_raw_sig \<theta> s') n"
            by (auto simp add:to_trans_raw_sig_def)
          hence "inf_time (to_trans_raw_sig  (\<theta>(t := Some \<circ> \<sigma>))) s' t' = inf_time (to_trans_raw_sig \<theta>) s' t'"
            by (meson \<open>t' < t\<close> inf_time_equal_when_same_trans_upto_strict)
          hence "signal_of (def s')  (\<theta>(t := Some \<circ> \<sigma>)) s' t' = signal_of (def s') \<theta> s' t'"
            unfolding to_signal_def comp_def using `t' < t`
            by (auto dest!: inf_time_at_most split:option.splits simp add: to_trans_raw_sig_def)
          hence " snd (worldline_raw t \<sigma> \<theta> def \<tau>) s' t' = signal_of (def s')  (\<theta>(t := Some \<circ> \<sigma>)) s' t'"
            unfolding worldline_raw_def using `t' < t` by auto }
        moreover
        { assume "t \<le> t'"
         have "\<tau> = 0"
            using `quiet \<tau> \<gamma>` unfolding quiet_def by meson
          hence inf_none: "inf_time (to_trans_raw_sig \<tau>) s' t' = None"
            unfolding inf_time_def  by (simp add: keys_def to_trans_raw_sig_def zero_fun_def)
          have *: "keys (to_trans_raw_sig  (\<theta>(t := Some \<circ> \<sigma>)) s') = insert t (keys (to_trans_raw_sig \<theta> s'))"
            by (auto simp add: to_trans_raw_sig_def keys_def zero_option_def)
          have "(\<forall>n\<ge>t. \<theta> n = 0)"
            using 2(4) unfolding context_invariant_def by auto
          hence **: " \<forall>k\<in> (keys (to_trans_raw_sig \<theta> s')). k < t"
            unfolding to_trans_raw_sig_def
            by (metis domIff dom_def keys_def leI zero_fun_def zero_option_def)
          have "inf_time (to_trans_raw_sig (\<theta>(t := Some \<circ> \<sigma>))) s' t' = Some t"
          proof -
            have "\<exists>k\<in>keys (to_trans_raw_sig (\<theta>(t := Some \<circ> \<sigma>)) s'). k \<le> t'"
              using * `t \<le> t'` by auto
            moreover have "(GREATEST k. k \<in> keys (to_trans_raw_sig (\<theta>(t := Some \<circ> \<sigma>)) s') \<and> k \<le> t') = t"
            proof (rule Greatest_equality)
              show "t \<in> keys (to_trans_raw_sig (\<theta>(t := Some \<circ> \<sigma>)) s') \<and> t \<le> t'"
                using * `t \<le> t'` by auto
            next
              show "\<And>y. y \<in> keys (to_trans_raw_sig (\<theta>(t := Some \<circ> \<sigma>)) s') \<and> y \<le> t' \<Longrightarrow> y \<le> t"
                unfolding * using ** by auto
            qed
            ultimately show ?thesis
              unfolding inf_time_def  by auto
          qed
          moreover have "the ((to_trans_raw_sig (\<theta>(t := Some \<circ> \<sigma>)) s') t) = \<sigma> s'"
            using 2(2) unfolding to_trans_raw_sig_def by auto
          ultimately have "signal_of (\<sigma> s') \<tau> s' t' = signal_of (def s') (\<theta>(t := Some \<circ> \<sigma>)) s' t'"
            using inf_none unfolding to_signal_def comp_def
            by (simp add: inf_time_def)
          hence " snd (worldline_raw t \<sigma> \<theta> def \<tau>) s' t' = signal_of (def s') (\<theta>(t := Some \<circ> \<sigma>)) s' t'"
            unfolding worldline_raw_def using `t \<le> t'` by auto }
        ultimately show "snd (worldline_raw t \<sigma> \<theta> def \<tau>) s' t' =  snd (def, \<lambda>s'. signal_of (def s') (\<theta>(t := Some \<circ> \<sigma>)) s') s' t'"
          by auto
      next
        show "get_time (worldline_raw t \<sigma> \<theta> def \<tau>) = get_time (def, \<lambda>s'. signal_of (def s') (\<theta>(t := Some \<circ> \<sigma>)) s')"
          by (simp add: worldline_raw_def)
      qed
      thus "snd (worldline2 t \<sigma> \<theta> def \<tau>) = snd (t, def, worldline_of_history def (\<theta>(t := Some \<circ> \<sigma>)))"
        unfolding worldline2_def  worldline_raw_def worldline_of_history_def by auto
    qed
    hence tw_def: "tw = (t, def, worldline_of_history def (\<theta>(t:= Some o \<sigma>)))"
      using `tw = worldline2 t \<sigma> \<theta> def \<tau>` by auto
    have *: "\<forall>tw'. tw, cs \<Rightarrow>\<^sub>c tw' \<longrightarrow> next_time_world tw' = fst tw + 1 \<and> snd tw = snd tw'"
    proof (rule, rule)
      fix tw'
      assume "tw, cs \<Rightarrow>\<^sub>c tw'"
      hence "fst tw = fst tw'"
        using fst_world_conc_exec  by metis
      hence "fst tw' = t"
        using tw_def by auto
      obtain theta where des: "destruct_worldline tw = (t, \<sigma>, \<gamma>, theta, def, \<tau>)"
        and sig_eq: "\<And>k s. signal_of (def s) \<theta> s k = signal_of (def s) theta s k"
        using "2.prems"(1) "2.prems"(2) "2.prems"(8) destruct_worldline_correctness4 by blast
      have "b_conc_exec t \<sigma> \<gamma> \<theta> def cs \<tau> \<tau>"
        using `quiet \<tau> \<gamma>`  by (metis b_conc_exec_empty_event quiet_def)
      moreover have "b_conc_exec t \<sigma> \<gamma> theta def cs \<tau> \<tau>"
        using `quiet \<tau> \<gamma>`  by (metis b_conc_exec_empty_event quiet_def)
      ultimately have "tw' = tw"
        using `tw, cs \<Rightarrow>\<^sub>c tw'` des `tw = worldline2 t \<sigma> \<theta> def \<tau>`
        by (smt b_conc_exec_deterministic fst_conv snd_conv world_conc_exec_cases worldline2_constructible)
      have "derivative_raw (snd tw') (fst tw') = \<tau>"
        unfolding `tw' = tw` using `tw = worldline2 t \<sigma> \<theta> def \<tau>` 2(4) unfolding context_invariant_def
        by (simp add: "2.prems"(8) derivative_raw_of_worldline2)
      thus "next_time_world tw' = fst tw + 1 \<and> snd tw = snd tw'"
        using 2(2) unfolding next_time_world_def Let_def `fst tw' = t` quiet_def next_time_def
        using \<open>fst tw' = t\<close> \<open>tw' = tw\<close> by auto
    qed
    obtain \<theta>' where des: "destruct_worldline tw = (t, \<sigma>, \<gamma>, \<theta>', def, \<tau>)" and
      "\<And>s k. signal_of (def s) \<theta> s k = signal_of (def s) \<theta>' s k"
      using `tw = worldline2 t \<sigma> \<theta> def \<tau>`
      by (meson "2.prems"(2) "2.prems"(8) destruct_worldline_correctness4)
    moreover have "tw , cs \<Rightarrow>\<^sub>c tw"
    proof (intro world_conc_exec.intros)
      show "destruct_worldline tw = (t, \<sigma>, \<gamma>, \<theta>', def, \<tau>)"
        using des by auto
    next
      have "t , \<sigma> , \<gamma> , \<theta>, def  \<turnstile> <cs , \<tau>> \<longrightarrow>\<^sub>c \<tau>"
        using `quiet \<tau> \<gamma>`  by (metis b_conc_exec_empty_event quiet_def)
      thus "t, \<sigma>, \<gamma>, \<theta>', def \<turnstile> <cs, \<tau>> \<longrightarrow>\<^sub>c \<tau>"
        using b_conc_exec_mono_wrt_history  calculation(2) by blast
    next
      show " worldline2 t \<sigma> \<theta>' def \<tau> = tw"
        using des worldline2_constructible by blast
    qed
    ultimately have "P (fst tw + 1, snd tw)"
      using 2(6) `P tw` tw_def unfolding conc_hoare_valid_def
      by (metis "*")
    { fix time
      assume "time > fst tw"
      have "\<forall>tw'. (time, snd tw), cs \<Rightarrow>\<^sub>c tw' \<longrightarrow> next_time_world tw' = time + 1 \<and> snd tw = snd tw'"
      proof (rule, rule)
        fix tw'
        assume "(time, snd tw), cs \<Rightarrow>\<^sub>c tw'"
        hence "time = fst tw'"
          using fst_world_conc_exec by (metis fst_conv)
        have "\<tau> = 0"
          using \<open>quiet \<tau> \<gamma>\<close> unfolding quiet_def by meson
        have "\<forall>n \<ge> t. \<theta> n = 0" and "\<forall>n \<le> t. \<tau> n = 0"
          using \<open>context_invariant t \<sigma> \<gamma> \<theta> def \<tau>\<close> unfolding context_invariant_def by auto
        hence "\<exists>theta. destruct_worldline (time, snd tw) = (time, \<sigma>, {}, theta, def, \<tau>) \<and>
               (\<forall>k s. signal_of (def s) (\<theta>(t := Some o \<sigma>)) s k = signal_of (def s) theta s k)"
        proof -
          have *: "destruct_worldline (time, snd tw) = (time, \<sigma>, {}, derivative_hist_raw (snd tw) time, def, \<tau>)"
          proof -
            have "snd tw = (def, worldline_of_history def (\<theta>(t:= Some o \<sigma>)))"
              using tw_def by auto
            have "\<theta> time = 0"
              using `time > fst tw` \<open>\<forall>n \<ge> t. \<theta> n = 0\<close> "2.prems"(1) by (simp add: "2.prems"(1))
            { fix s
              have "wline_of tw s time = signal_of (def s) (\<theta> (t:=Some o \<sigma>)) s time"
                using \<open>tw = (t, def, worldline_of_history def (\<theta>(t:= Some o \<sigma>)))\<close>
                unfolding worldline_of_history_def by auto
              also have "... = signal_of (def s) (\<theta> (t:=Some o \<sigma>)) s time"
                using signal_of_less[of "\<theta>(t := Some o \<sigma>)" "t + 1"] by simp
              also have "... = \<sigma> s"
                by (smt \<open>\<forall>n\<ge>t. \<theta> n = 0\<close> \<open>get_time tw < time\<close> fst_conv fun_upd_other fun_upd_same
                less_imp_le_nat nat_neq_iff signal_of_less_ind trans_some_signal_of tw_def)
              hence "wline_of tw s time = \<sigma> s"
                using \<open>wline_of tw s time = signal_of (def s) (\<theta>(t := Some \<circ> \<sigma>)) s time\<close>  by simp }
            note * = this
            hence "(\<lambda>s. wline_of tw s time) = \<sigma>"
              by auto
            hence 1: "(\<lambda>s. wline_of (time, snd tw) s (fst (time, snd tw))) = \<sigma>"
              by auto
            have 2: "{s. wline_of tw s time \<noteq> signal_of (def s) (derivative_hist_raw (snd tw) time) s t} = {}"
              using *
              by (metis (mono_tags, lifting) Collect_empty_eq \<open>get_time tw < time\<close> des
              destruct_worldline_correctness(2) destruct_worldline_correctness(6)
              destruct_worldline_def fst_conv signal_of_derivative_hist_raw
              worldline2_constructible)
            { fix s n
              assume "n \<ge> time"
              have "wline_of tw s n = signal_of (def s) (\<theta> (t:=Some o \<sigma>)) s n"
                by (simp add: tw_def worldline_of_history_def)
              also have "... = signal_of (def s) (\<theta> (t := Some o \<sigma>)) s time"
                using \<open>n \<ge> time\<close>
                by (intro signal_of_less_ind')
                   (metis \<open>\<forall>n\<ge>t. \<theta> n = 0\<close> \<open>fst tw < time\<close> dual_order.trans fst_conv fun_upd_apply leD
                   order.strict_implies_order tw_def zero_fun_def)
              also have "... = wline_of tw s time"
                by (simp add: tw_def worldline_of_history_def)
              finally have "wline_of tw s n = wline_of tw s time"
                by auto }
            hence 3: "derivative_raw (snd tw) time = \<tau>"
              using derivative_raw_alt_def[where tw="(time, snd tw)"] \<open>\<tau> = 0\<close>
              by (metis comp_apply fst_conv snd_conv)
            have "fst tw = t"
              by (simp add: "2.prems"(1))
            hence "\<And>s k . signal_of (def s) (derivative_hist_raw (snd tw) time) s (time - 1) =
                          signal_of (def s) (derivative_hist_raw (snd tw) time ) s t"
              using `time > fst tw`
              by (smt "2.prems"(1) Suc_diff_1 Suc_lessI \<open>\<tau> = 0\<close> diff_less fst_conv le_add2
              le_add_same_cancel2 le_less_trans nat_neq_iff order.strict_implies_order
              signal_of_derivative_hist_raw signal_of_empty snd_conv worldline2_def
              worldline_raw_def zero_less_one)
            hence new2: "{s. wline_of tw s time \<noteq> signal_of (def s) (derivative_hist_raw (snd tw) time) s (time - 1)} = {}"
              using 2 by auto
            have "fst (snd tw) = def"
              by (simp add: \<open>snd tw = (def, worldline_of_history def (\<theta>(t := Some \<circ> \<sigma>)))\<close>)
            with 1 new2 3 show ?thesis
              unfolding destruct_worldline_def Let_def
              by auto
          qed
          { fix k s
            have "signal_of (def s) (\<theta>(t := Some o \<sigma>)) s k = signal_of (def s) (derivative_hist_raw (snd tw) time) s k"
            proof -
              have "fst tw = t"
                by (simp add: tw_def)
              have "k \<le> time \<or> time < k"
                by auto
              moreover
              { assume "k \<le> time"
                hence "signal_of (def s) (\<theta>(t := Some o \<sigma>)) s k = signal_of (def s) (derivative_hist_raw (snd tw) time) s k"
                  using \<open>fst tw < time\<close> \<open>fst tw = t\<close>
                  by (smt Suc_diff_1 Suc_leI \<open>\<tau> = 0\<close> \<open>worldline2 t \<sigma> \<theta> def \<tau> = (t, def,
                  worldline_of_history def (\<theta>(t := Some \<circ> \<sigma>)))\<close> dual_order.order_iff_strict
                  eq_fst_iff le_add2 le_add_same_cancel2 not_le signal_of_derivative_hist_raw
                  signal_of_derivative_hist_raw2 signal_of_empty snd_conv tw_def worldline2_def
                  worldline_of_history_def worldline_raw_def) }
              moreover
              { assume "time < k"
                hence "t < k" and "time \<le> k"
                  using \<open>fst tw < time\<close> tw_def by auto
                hence " inf_time (to_trans_raw_sig (\<theta>(t := Some o \<sigma>))) s k = Some t"
                  by (meson \<open>\<forall>n\<ge>t. \<theta> n = 0\<close> \<open>t < k\<close> inf_time_update less_or_eq_imp_le)
                hence "signal_of (def s) (\<theta>(t := Some o \<sigma>)) s k = \<sigma> s"
                  unfolding to_signal_def comp_def  by (simp add: to_trans_raw_sig_def)
                have "signal_of (def s) (derivative_hist_raw (snd tw) time) s k = wline_of tw s (time - 1)"
                  using signal_of_derivative_hist_raw2[OF `time \<le> k`]
                  by (smt \<open>get_time tw < time\<close> comp_apply fst_conv neq0_conv not_less_zero snd_conv tw_def)
                also have "... = worldline_of_history def (\<theta>(t:= Some o \<sigma>)) s t"
                  unfolding tw_def
                  by (smt Suc_diff_1 Suc_lessI \<open>\<tau> = 0\<close> \<open>get_time tw < time\<close> \<open>get_time tw = t\<close>
                  \<open>worldline2 t \<sigma> \<theta> def \<tau> = (t, def, worldline_of_history def (\<theta>(t := Some \<circ> \<sigma>)))\<close>
                  comp_apply dual_order.strict_trans2 gr_implies_not_zero less_imp_le_nat
                  less_irrefl_nat linorder_neqE_nat signal_of_empty snd_conv worldline2_def
                  worldline_raw_def)
                also have "... = signal_of (def s) (\<theta>(t:= Some o \<sigma>)) s t"
                  unfolding worldline_of_history_def by auto
                finally have "signal_of (def s) (\<theta>(t := Some o \<sigma>)) s k = signal_of (def s) (derivative_hist_raw (snd tw) time) s k"
                  by (metis \<open>signal_of (def s) (\<theta>(t := Some \<circ> \<sigma>)) s k = \<sigma> s\<close> fun_upd_same trans_some_signal_of) }
              ultimately show "signal_of (def s) (\<theta>(t := Some \<circ> \<sigma>)) s k = signal_of (def s) (derivative_hist_raw (snd tw) time) s k"
                by auto
            qed }
          with * show ?thesis
            by auto
        qed
        then obtain theta where des: "destruct_worldline (time, snd tw) = (time, \<sigma>, {}, theta, def, \<tau>)"
          and "\<And>k s. signal_of (def s) (\<theta>(t:= Some o \<sigma>)) s k = signal_of (def s) theta s k"
          by blast
        have "b_conc_exec time \<sigma> {} theta def cs \<tau> \<tau>"
          by (simp add: b_conc_exec_empty_event)
        hence "(time, snd tw), cs \<Rightarrow>\<^sub>c (worldline2  time \<sigma> theta def \<tau>)"
          using des world_conc_exec.intros by blast
        moreover have "(time, snd tw) = worldline2 time \<sigma> theta def \<tau>"
          using `tw = worldline2 t \<sigma> \<theta> def \<tau>`  using des worldline2_constructible by blast
        ultimately have "(time, snd tw), cs \<Rightarrow>\<^sub>c (time, snd tw)"
          by auto
        hence "(time, snd tw) = tw'"
          using world_conc_exec_deterministic  by (metis \<open>(time, snd tw) , cs \<Rightarrow>\<^sub>c tw'\<close>)
        hence "derivative_raw (snd tw') (fst tw') = \<tau>"
          by (metis "2.prems"(8) \<open>(time, snd tw) = worldline2 time \<sigma> theta def \<tau>\<close> \<open>\<tau> = 0\<close> \<open>time =
          get_time tw'\<close> derivative_raw_of_worldline2 zero_fun_def)
        thus " next_time_world tw' = time + 1 \<and> snd tw = snd tw'"
          using 2(2) unfolding next_time_world_def Let_def
          using \<open>(time, snd tw) = tw'\<close> \<open>\<tau> = 0\<close> by force
      qed }
    hence "\<And>time. time > fst tw \<Longrightarrow> \<forall>tw'. (time, snd tw), cs \<Rightarrow>\<^sub>c tw' \<longrightarrow> next_time_world tw' = time + 1 \<and> snd tw = snd tw'"
      by auto
    with * have **: "\<And>time. time \<ge> fst tw \<Longrightarrow> \<forall>tw'. (time, snd tw), cs \<Rightarrow>\<^sub>c tw' \<longrightarrow> next_time_world tw' = time + 1 \<and> snd tw = snd tw'"
      by (metis (full_types) dual_order.order_iff_strict prod.collapse)
    have always_progress: "\<And>time. get_time tw \<le> time \<Longrightarrow> \<exists>tw'. (time, snd tw) , cs \<Rightarrow>\<^sub>c tw'"
    proof -
      fix time
      have "\<tau> = 0"
        by (meson "2.hyps"(2) quiet_def)
      assume "get_time tw \<le> time"
      hence "get_time tw = time \<or> get_time tw < time"
        by auto
      moreover
      { assume "get_time tw = time"
        hence "(time, snd tw) = tw"
          by auto
        hence "\<exists>tw'. (time, snd tw), cs \<Rightarrow>\<^sub>c tw'"
          by (metis \<open>tw , cs \<Rightarrow>\<^sub>c tw\<close>) }
      moreover
      { assume "get_time tw < time"
        hence "\<exists>theta. destruct_worldline (time, snd tw) = (time, \<sigma>, {}, theta, def, \<tau>) \<and>
               (\<forall>k s. signal_of (def s) (\<theta>(t := Some o \<sigma>)) s k = signal_of (def s) theta s k)"
        proof -
          have *: "destruct_worldline (time, snd tw) = (time, \<sigma>, {}, derivative_hist_raw (snd tw) time, def, \<tau>)"
          proof -
            have "snd tw = (def, worldline_of_history def (\<theta>(t:= Some o \<sigma>)))"
              using tw_def by auto
            have "\<theta> time = 0"
              using `time > fst tw` \<open>\<forall>n \<ge> t. \<theta> n = 0\<close> "2.prems"(1) by (simp add: "2.prems"(1))
            { fix s
              have "wline_of tw s time = signal_of (def s) (\<theta> (t:=Some o \<sigma>)) s time"
                using \<open>tw = (t, def, worldline_of_history def (\<theta>(t:= Some o \<sigma>)))\<close>
                unfolding worldline_of_history_def by auto
              also have "... = signal_of (def s) (\<theta> (t:=Some o \<sigma>)) s time"
                using signal_of_less[of "\<theta>(t := Some o \<sigma>)" "t + 1"] by simp
              also have "... = \<sigma> s"
                by (smt \<open>\<forall>n\<ge>t. \<theta> n = 0\<close> \<open>get_time tw < time\<close> fst_conv fun_upd_other fun_upd_same
                less_imp_le_nat nat_neq_iff signal_of_less_ind trans_some_signal_of tw_def)
              hence "wline_of tw s time = \<sigma> s"
                using \<open>wline_of tw s time = signal_of (def s) (\<theta>(t := Some \<circ> \<sigma>)) s time\<close>  by simp }
            note * = this
            hence "(\<lambda>s. wline_of tw s time) = \<sigma>"
              by auto
            hence 1: "(\<lambda>s. wline_of (time, snd tw) s (fst (time, snd tw))) = \<sigma>"
              by auto
            have 2: "{s. wline_of tw s time \<noteq> signal_of (def s) (derivative_hist_raw (snd tw) time) s t} = {}"
              using *
              by (metis (mono_tags, lifting) Collect_empty_eq \<open>get_time tw < time\<close> des
              destruct_worldline_correctness(2) destruct_worldline_correctness(6)
              destruct_worldline_def fst_conv signal_of_derivative_hist_raw
              worldline2_constructible)
            { fix s n
              assume "n \<ge> time"
              have "wline_of tw s n = signal_of (def s) (\<theta> (t:=Some o \<sigma>)) s n"
                by (simp add: tw_def worldline_of_history_def)
              also have "... = signal_of (def s) (\<theta> (t := Some o \<sigma>)) s time"
                using \<open>n \<ge> time\<close>
                by (intro signal_of_less_ind')
                   (metis \<open>\<forall>n\<ge>t. \<theta> n = 0\<close> \<open>fst tw < time\<close> dual_order.trans fst_conv fun_upd_apply leD
                   order.strict_implies_order tw_def zero_fun_def)
              also have "... = wline_of tw s time"
                by (simp add: tw_def worldline_of_history_def)
              finally have "wline_of tw s n = wline_of tw s time"
                by auto }
            hence 3: "derivative_raw (snd tw) time = \<tau>"
              using derivative_raw_alt_def[where tw="(time, snd tw)"] \<open>\<tau> = 0\<close>
              by (metis comp_apply fst_conv snd_conv)
            have "fst tw = t"
              by (simp add: "2.prems"(1))
            hence "\<And>s k . signal_of (def s) (derivative_hist_raw (snd tw) time) s (time - 1) =
                          signal_of (def s) (derivative_hist_raw (snd tw) time ) s t"
              using `time > fst tw`
              by (smt "2.prems"(1) Suc_diff_1 Suc_lessI \<open>\<tau> = 0\<close> diff_less fst_conv le_add2
              le_add_same_cancel2 le_less_trans nat_neq_iff order.strict_implies_order
              signal_of_derivative_hist_raw signal_of_empty snd_conv worldline2_def
              worldline_raw_def zero_less_one)
            hence new2: "{s. wline_of tw s time \<noteq> signal_of (def s) (derivative_hist_raw (snd tw) time) s (time - 1)} = {}"
              using 2 by auto
            have "fst (snd tw) = def"
              by (simp add: \<open>snd tw = (def, worldline_of_history def (\<theta>(t := Some \<circ> \<sigma>)))\<close>)
            with 1 new2 3 show ?thesis
              unfolding destruct_worldline_def Let_def
              by auto
          qed
          { fix k s
            have "signal_of (def s) (\<theta>(t := Some o \<sigma>)) s k = signal_of (def s) (derivative_hist_raw (snd tw) time) s k"
            proof -
              have "fst tw = t"
                by (simp add: tw_def)
              have "k \<le> time \<or> time < k"
                by auto
              moreover
              { assume "k \<le> time"
                hence "signal_of (def s) (\<theta>(t := Some o \<sigma>)) s k = signal_of (def s) (derivative_hist_raw (snd tw) time) s k"
                  using \<open>fst tw < time\<close> \<open>fst tw = t\<close>
                  by (smt Suc_diff_1 Suc_leI \<open>\<tau> = 0\<close> \<open>worldline2 t \<sigma> \<theta> def \<tau> = (t, def,
                  worldline_of_history def (\<theta>(t := Some \<circ> \<sigma>)))\<close> dual_order.order_iff_strict
                  eq_fst_iff le_add2 le_add_same_cancel2 not_le signal_of_derivative_hist_raw
                  signal_of_derivative_hist_raw2 signal_of_empty snd_conv tw_def worldline2_def
                  worldline_of_history_def worldline_raw_def) }
              moreover
              { assume "time < k"
                hence "t < k" and "time \<le> k"
                  using \<open>fst tw < time\<close> tw_def by auto
                hence " inf_time (to_trans_raw_sig (\<theta>(t := Some o \<sigma>))) s k = Some t"
                  by (meson \<open>\<forall>n\<ge>t. \<theta> n = 0\<close> \<open>t < k\<close> inf_time_update less_or_eq_imp_le)
                hence "signal_of (def s) (\<theta>(t := Some o \<sigma>)) s k = \<sigma> s"
                  unfolding to_signal_def comp_def  by (simp add: to_trans_raw_sig_def)
                have "signal_of (def s) (derivative_hist_raw (snd tw) time) s k = wline_of tw s (time - 1)"
                  using signal_of_derivative_hist_raw2[OF `time \<le> k`]
                  by (smt \<open>get_time tw < time\<close> comp_apply fst_conv neq0_conv not_less_zero snd_conv tw_def)
                also have "... = worldline_of_history def (\<theta>(t:= Some o \<sigma>)) s t"
                  unfolding tw_def
                  by (smt Suc_diff_1 Suc_lessI \<open>\<tau> = 0\<close> \<open>get_time tw < time\<close> \<open>get_time tw = t\<close>
                  \<open>worldline2 t \<sigma> \<theta> def \<tau> = (t, def, worldline_of_history def (\<theta>(t := Some \<circ> \<sigma>)))\<close>
                  comp_apply dual_order.strict_trans2 gr_implies_not_zero less_imp_le_nat
                  less_irrefl_nat linorder_neqE_nat signal_of_empty snd_conv worldline2_def
                  worldline_raw_def)
                also have "... = signal_of (def s) (\<theta>(t:= Some o \<sigma>)) s t"
                  unfolding worldline_of_history_def by auto
                finally have "signal_of (def s) (\<theta>(t := Some o \<sigma>)) s k = signal_of (def s) (derivative_hist_raw (snd tw) time) s k"
                  by (metis \<open>signal_of (def s) (\<theta>(t := Some \<circ> \<sigma>)) s k = \<sigma> s\<close> fun_upd_same trans_some_signal_of) }
              ultimately show "signal_of (def s) (\<theta>(t := Some \<circ> \<sigma>)) s k = signal_of (def s) (derivative_hist_raw (snd tw) time) s k"
                by auto
            qed }
          with * show ?thesis
            by auto
        qed
        then obtain theta where des: "destruct_worldline (time, snd tw) = (time, \<sigma>, {}, theta, def, \<tau>)"
          and "\<And>k s. signal_of (def s) (\<theta>(t:= Some o \<sigma>)) s k = signal_of (def s) theta s k"
          by blast
        hence "b_conc_exec time \<sigma> {} theta def cs \<tau> \<tau>"
          by (simp add: b_conc_exec_empty_event)
        hence "\<exists>tw'. (time, snd tw), cs \<Rightarrow>\<^sub>c tw'"
          using des world_conc_exec.intros by blast }
      ultimately show "\<exists>tw'. (time, snd tw), cs \<Rightarrow>\<^sub>c tw'"
        by auto
    qed
    have "P (maxtime, snd tw)"
      using \<open>t \<le> maxtime\<close>
    proof (induction "maxtime - fst tw" arbitrary:maxtime)
      case 0
      then show ?case using `P tw`  using tw_def by auto
    next
      case (Suc x)
      hence "x = (maxtime - 1) - fst tw"
        by auto
      hence "P (maxtime - 1, snd tw)"
        using Suc
        by (metis One_nat_def diff_diff_cancel diff_is_0_eq' dual_order.order_iff_strict fst_conv
        leI tw_def)
      have "maxtime - 1 \<ge> fst tw"
        using Suc by auto
      have "\<forall>tw'. (maxtime - 1, snd tw), cs \<Rightarrow>\<^sub>c tw' \<longrightarrow> next_time_world tw' = maxtime \<and> snd tw = snd tw'"
        using **[OF `maxtime - 1 \<ge> fst tw`]
        by (metis Suc.hyps(2) Suc_eq_plus1 Suc_inject \<open>x = maxtime - 1 - fst tw\<close> add_eq_if diff_0_eq_0)
      have "\<exists>tw'. (maxtime - 1, snd tw) , cs \<Rightarrow>\<^sub>c tw'"
        using always_progress \<open>get_time tw \<le> maxtime - 1\<close> by blast
      with 2(6) show ?case
        using `P (maxtime - 1, snd tw)` unfolding conc_hoare_valid_def
        by (metis (full_types) \<open>\<forall>tw'. (maxtime - 1, snd tw) , cs \<Rightarrow>\<^sub>c tw' \<longrightarrow> next_time_world tw' = maxtime \<and> snd tw = snd tw'\<close>)
    qed
    hence "P (maxtime + 1, snd tw)"
      using ** "2.hyps"(1) "2.prems"(4) always_progress unfolding conc_hoare_valid_def
      by (metis eq_fst_iff tw_def)
    moreover have "snd tw =  worldline_raw (maxtime + 1) \<sigma> (\<theta>(t := Some \<circ> \<sigma>)) def 0"
      unfolding tw_def snd_conv
    proof (rule, rule_tac[2] ext, rule_tac[2] ext)
      fix s' t'
      have "t' < maxtime + 1 \<or> maxtime + 1 \<le> t'"
        by auto
      moreover
      { assume "t' < maxtime + 1"
        hence "snd (worldline_raw (maxtime + 1) \<sigma> (\<theta>(t := Some \<circ> \<sigma>)) def 0) s' t' = signal_of (def s') (\<theta>(t := Some \<circ> \<sigma>)) s' t'"
          unfolding worldline_raw_def by auto
        also have "... = worldline_of_history def (\<theta>(t := Some \<circ> \<sigma>)) s' t'"
          unfolding worldline_of_history_def by auto
        finally have "worldline_of_history def (\<theta>(t:= Some o \<sigma>)) s' t' = snd (worldline_raw (maxtime + 1) \<sigma> (\<theta>(t := Some \<circ> \<sigma>)) def 0) s' t'"
          by auto }
      moreover
      { assume " maxtime + 1 \<le> t'"
        hence "snd (worldline_raw (maxtime + 1) \<sigma> (\<theta>(t := Some \<circ> \<sigma>)) def 0) s' t' = signal_of (\<sigma> s') 0 s' t'"
          unfolding worldline_raw_def by auto
        also have "... = \<sigma> s'"
          by (meson signal_of_empty)
        also have "... = signal_of (def s') (\<theta>(t := Some \<circ> \<sigma>)) s' t"
          by (metis fun_upd_same trans_some_signal_of)
        also have "... = signal_of (def s') (\<theta>(t := Some o \<sigma>)) s' t'"
          using \<open>\<forall>n. t \<le> n \<longrightarrow>  \<theta> n = 0\<close> \<open>t \<le> maxtime\<close> \<open>maxtime + 1 \<le> t'\<close>
          by (intro sym[OF signal_of_less_ind'])(simp add: zero_fun_def, linarith)
        also have "... = worldline_of_history def (\<theta>(t:= Some o \<sigma>)) s' t'"
          unfolding worldline_of_history_def by auto
        finally have "worldline_of_history def (\<theta>(t:= Some o \<sigma>)) s' t' = snd (worldline_raw (maxtime + 1) \<sigma> (\<theta>(t := Some \<circ> \<sigma>)) def 0) s' t'"
          by auto }
      ultimately show "snd (def, worldline_of_history def (\<theta>(t := Some \<circ> \<sigma>))) s' t' = snd (worldline_raw (maxtime + 1) \<sigma> (\<theta>(t := Some \<circ> \<sigma>)) def 0) s' t'"
        by auto
    qed (simp add: worldline_raw_def)
    ultimately show ?case
      using "2.prems"(3) snd_conv tw_def
      by (simp add: \<open>tw' = (get_time (maxtime + 1, \<sigma>, \<theta>(t := Some \<circ> \<sigma>), 0), worldline_raw (get_time
      (maxtime + 1, \<sigma>, \<theta>(t := Some \<circ> \<sigma>), 0)) (get_state (maxtime + 1, \<sigma>, \<theta>(t := Some \<circ> \<sigma>), 0))
      (get_beh (maxtime + 1, \<sigma>, \<theta>(t := Some \<circ> \<sigma>), 0)) def (get_trans (maxtime + 1, \<sigma>, \<theta>(t := Some \<circ>
      \<sigma>), 0)))\<close>)
  next
    case (3 t maxtime \<sigma> \<gamma> \<theta> cs \<tau>)
    hence "tw' = tw"
      by (simp add: worldline2_def)
    then show ?case
      using `P tw` by auto
  qed
qed

lemma conc_sim_soundness:
  assumes "\<turnstile>\<^sub>s \<lbrace>P\<rbrace> cs \<lbrace>Q\<rbrace>"
  assumes "nonneg_delay_conc cs" and "conc_stmt_wf cs"
  shows "\<Turnstile>\<^sub>s \<lbrace>P\<rbrace> cs \<lbrace>Q\<rbrace>"
  using assms
proof (induction rule:conc_sim.induct)
  case (While P cs)
  hence " \<Turnstile> \<lbrace>\<lambda>tw. P tw\<rbrace> cs \<lbrace>\<lambda>tw. P (next_time_world tw, snd tw)\<rbrace>"
    using soundness_conc_hoare[OF While(1)] by auto
  then show ?case
    unfolding sim_hoare_valid_def using while_soundness2[OF _ _ _ While(2) While(3)] by auto
next
  case (Conseq_sim P' P cs Q Q')
  then show ?case by (metis (full_types) sim_hoare_valid_def)
qed

subsection \<open>Initialisation\<close>

inductive world_init_exec :: "nat \<times> 'signal worldline_init \<Rightarrow> 'signal conc_stmt \<Rightarrow> nat \<times> 'signal worldline_init \<Rightarrow> bool"
  ("(_ , _) \<Rightarrow>\<^sub>I _") where
  "     destruct_worldline tw = (t, \<sigma>, \<gamma>, \<theta>, def, \<tau>)
   \<Longrightarrow>  init' t \<sigma> \<gamma> \<theta> def cs \<tau> \<tau>'
   \<Longrightarrow>  worldline2 t \<sigma> \<theta> def \<tau>' = tw'
   \<Longrightarrow>  world_init_exec tw cs tw'"

inductive_cases world_init_exec_cases [elim!]: "world_init_exec tw (process sl : ss) tw'"
                                               "world_init_exec tw (cs1 || cs2) tw'"

inductive
  init_hoare :: "'signal assn2 \<Rightarrow> 'signal conc_stmt \<Rightarrow> 'signal assn2 \<Rightarrow> bool"
  ("\<turnstile>\<^sub>I (\<lbrace>(1_)\<rbrace>/ (_)/ \<lbrace>(1_)\<rbrace>)" 50)
  where
  SingleI:    "\<turnstile> [P] ss [Q] \<Longrightarrow> \<turnstile>\<^sub>I \<lbrace>P\<rbrace> process sl : ss \<lbrace>Q\<rbrace>"
| ParallelI:  "\<turnstile>\<^sub>I \<lbrace>P\<rbrace> cs\<^sub>1 \<lbrace>R\<rbrace> \<Longrightarrow> \<turnstile>\<^sub>I \<lbrace>R\<rbrace> cs\<^sub>2 \<lbrace>Q\<rbrace> \<Longrightarrow> conc_stmt_wf (cs\<^sub>1 || cs\<^sub>2) \<Longrightarrow> \<turnstile>\<^sub>I \<lbrace>P\<rbrace> cs\<^sub>1 || cs\<^sub>2 \<lbrace>Q\<rbrace>"
| ParallelI2: "\<turnstile>\<^sub>I \<lbrace>P\<rbrace> cs\<^sub>2 \<lbrace>R\<rbrace> \<Longrightarrow> \<turnstile>\<^sub>I \<lbrace>R\<rbrace> cs\<^sub>1 \<lbrace>Q\<rbrace> \<Longrightarrow> conc_stmt_wf (cs\<^sub>1 || cs\<^sub>2) \<Longrightarrow> \<turnstile>\<^sub>I \<lbrace>P\<rbrace> cs\<^sub>1 || cs\<^sub>2 \<lbrace>Q\<rbrace>"
| ConseqI:    "\<lbrakk>\<forall>w. P' w \<longrightarrow> P w; \<turnstile>\<^sub>I \<lbrace>P\<rbrace> cs \<lbrace>Q\<rbrace>; \<forall>w. Q w \<longrightarrow> Q' w\<rbrakk> \<Longrightarrow> \<turnstile>\<^sub>I \<lbrace>P'\<rbrace> cs \<lbrace>Q\<rbrace>"
| ConjI:      "\<turnstile>\<^sub>I \<lbrace>P\<rbrace> cs \<lbrace>Q1\<rbrace> \<Longrightarrow> \<turnstile>\<^sub>I \<lbrace>P\<rbrace> cs \<lbrace>Q2\<rbrace> \<Longrightarrow> \<turnstile>\<^sub>I \<lbrace>P\<rbrace> cs \<lbrace>\<lambda>tw. Q1 tw \<and> Q2 tw\<rbrace>"

definition
  init_hoare_valid :: "'signal assn2 \<Rightarrow> 'signal conc_stmt \<Rightarrow> 'signal assn2 \<Rightarrow> bool" ("\<Turnstile>\<^sub>I \<lbrace>(1_)\<rbrace>/ (_)/ \<lbrace>(1_)\<rbrace>" 50)
  where "\<Turnstile>\<^sub>I \<lbrace>P\<rbrace> cs \<lbrace>Q\<rbrace> \<longleftrightarrow>  (\<forall>tw tw'.  P tw \<and> (tw, cs \<Rightarrow>\<^sub>I tw') \<longrightarrow> Q tw')"

lemma parallelI_valid:
  assumes "\<Turnstile>\<^sub>I \<lbrace>P\<rbrace> c1 \<lbrace>R\<rbrace>" and "\<Turnstile>\<^sub>I \<lbrace>R\<rbrace> c2 \<lbrace>Q\<rbrace>" and "conc_stmt_wf (c1 || c2)"
  assumes "nonneg_delay_conc (c1 || c2)"
  shows "\<Turnstile>\<^sub>I \<lbrace>P\<rbrace> c1 || c2 \<lbrace>Q\<rbrace>"
  unfolding init_hoare_valid_def
proof rule+
  fix tw tw':: "nat \<times> 'a worldline_init"
  assume "P tw \<and> tw , c1 || c2 \<Rightarrow>\<^sub>I tw'"
  hence "P tw" and "tw, c1 || c2 \<Rightarrow>\<^sub>I tw'"
    by auto
  then obtain t \<sigma> \<gamma> \<theta> def \<tau> \<tau>' where des: "destruct_worldline tw = (t, \<sigma>, \<gamma>, \<theta>, def, \<tau>)" and
    *: "init' t \<sigma> \<gamma> \<theta> def (c1 || c2) \<tau> \<tau>'" and w'_def: "worldline2 t \<sigma> \<theta> def \<tau>' = tw'" and
    ci: "context_invariant t \<sigma> \<gamma> \<theta> def \<tau>"
    using destruct_worldline_exist  by (smt world_init_exec_cases(2) worldline2_constructible)
  then obtain \<tau>1 where \<tau>1_def: "init' t \<sigma> \<gamma> \<theta> def c1 \<tau> \<tau>1"
    by blast
  have "\<forall>s. non_stuttering (to_trans_raw_sig \<tau>1) \<sigma> s"
  proof
    fix s
    have "non_stuttering (to_trans_raw_sig \<tau>) \<sigma> s"
      using destruct_worldline_ensure_non_stuttering[OF des] by auto
    moreover have "\<And>n. n \<le> t \<Longrightarrow> \<tau> n = 0"
      using ci unfolding context_invariant_def by auto
    moreover have "nonneg_delay_conc c1" and "conc_stmt_wf c1"
      using assms(3-4) by auto
    ultimately show "non_stuttering (to_trans_raw_sig \<tau>1) \<sigma> s"
      using init'_preserves_non_stuttering[OF \<tau>1_def] by auto
  qed
  hence ci1: "context_invariant t \<sigma> \<gamma> \<theta> def \<tau>1"
    using init'_preserves_context_invariant[OF \<tau>1_def ci] assms(4) by simp
  obtain \<tau>2 where \<tau>2_def: "init' t \<sigma> \<gamma> \<theta> def c2 \<tau> \<tau>2"
    using * by blast
  hence ci2: "context_invariant t \<sigma> \<gamma> \<theta> def \<tau>2"
    using init'_preserves_context_invariant[OF \<tau>2_def ci] assms(4) by auto
  have \<tau>'_def: "init' t \<sigma> \<gamma> \<theta> def c2 \<tau>1 \<tau>'"
    using init'_sequential[OF assms(3)] *  \<tau>1_def by auto
  define tw1 where "tw1 = worldline2 t \<sigma> \<theta> def \<tau>1"
  hence "tw, c1 \<Rightarrow>\<^sub>I tw1"
    using des \<tau>1_def by (auto intro!: world_init_exec.intros)
  hence "R tw1"
    using assms(1) `P tw` unfolding init_hoare_valid_def by blast
  then obtain theta1 where des2: "destruct_worldline tw1 = (t, \<sigma>, \<gamma>, theta1, def, \<tau>1)" and
    beh_same: "\<And>k s. signal_of (def s) \<theta> s k = signal_of (def s) theta1 s k"
    using \<open>\<forall>s. non_stuttering (to_trans_raw_sig \<tau>1) \<sigma> s\<close> ci1 des destruct_worldline_correctness3
    destruct_worldline_ensure_non_stuttering_hist_raw tw1_def by blast
  have "context_invariant t \<sigma> \<gamma> theta1 def \<tau>1"
    using des2 worldline2_constructible by fastforce
  moreover have "nonneg_delay_conc c2"
    using assms(4) by auto
  moreover have "init' t \<sigma> \<gamma> theta1 def c2 \<tau>1 \<tau>'"
    by (metis \<open>\<forall>s. non_stuttering (to_trans_raw_sig \<tau>1) \<sigma> s\<close> \<tau>'_def ci1 des des2
    destruct_worldline_correctness2(5) destruct_worldline_ensure_non_stuttering_hist_raw tw1_def)
  have "worldline2 t \<sigma> theta1 def \<tau>' = worldline2 t \<sigma> \<theta> def \<tau>'"
    using beh_same \<tau>'_def ci1  unfolding worldline2_def worldline_raw_def by presburger
  hence "tw1, c2 \<Rightarrow>\<^sub>I tw'"
    using des2 \<open>init' t \<sigma> \<gamma> theta1 def c2 \<tau>1 \<tau>'\<close> w'_def world_init_exec.intros by blast
  with `R tw1` show "Q tw'"
    using assms(2) using init_hoare_valid_def by metis
qed

lemma parallelI_comp_commute':
  assumes "conc_stmt_wf (cs1 || cs2)"
  assumes "init' t \<sigma> \<gamma> \<theta> def (cs1 || cs2) \<tau> \<tau>'"
  shows "init' t \<sigma> \<gamma> \<theta> def (cs2 || cs1) \<tau> \<tau>'"
proof -
  have "disjnt (set (signals_from cs1)) (set (signals_from cs2))"
    using assms(1) unfolding conc_stmt_wf_def by (simp add: disjnt_def)
  thus ?thesis
    using van_tassel_second_prop' assms(2) init'.intros(2) by fastforce
qed

lemma world_init_exec_commute:
  assumes "tw, (cs1 || cs2) \<Rightarrow>\<^sub>I tw1"
  assumes "tw, (cs2 || cs1) \<Rightarrow>\<^sub>I tw2"
  assumes "conc_stmt_wf (cs1 || cs2)"
  shows "tw1 = tw2"
proof -
  obtain t \<sigma> \<gamma> \<theta> \<tau> def \<tau>' where "destruct_worldline tw = (t, \<sigma>, \<gamma>, \<theta>, def, \<tau>)" and
    "init' t \<sigma> \<gamma> \<theta> def (cs1 || cs2) \<tau> \<tau>'" and "worldline2 t \<sigma> \<theta> def \<tau>' = tw1"
    using assms(1)  by (smt world_init_exec_cases(2))
  hence "init' t \<sigma> \<gamma> \<theta> def (cs2 || cs1) \<tau> \<tau>'"
    using parallelI_comp_commute'[OF assms(3)] by auto
  thus ?thesis
    using assms(2) \<open>destruct_worldline tw = (t, \<sigma>, \<gamma>, \<theta>, def, \<tau>)\<close> \<open>worldline2 t \<sigma> \<theta> def \<tau>' = tw1\<close>
    by (smt fst_conv init'_deterministic snd_conv world_init_exec_cases(2))
qed

lemma soundness_init_hoare:
  assumes "\<turnstile>\<^sub>I \<lbrace>P\<rbrace> c \<lbrace>Q\<rbrace>"
  assumes "conc_stmt_wf c" and "nonneg_delay_conc c"
  shows   "\<Turnstile>\<^sub>I \<lbrace>P\<rbrace> c \<lbrace>Q\<rbrace>"
  using assms
proof (induction rule:init_hoare.induct)
  case (SingleI P ss Q sl)
  { fix tw  tw' :: "nat \<times> 'a worldline_init"
    assume as: "P tw \<and> (tw ,  process sl : ss \<Rightarrow>\<^sub>I tw')"
    then obtain t \<sigma> \<gamma> \<theta> \<tau> def \<tau>' where des: "destruct_worldline tw = (t, \<sigma>, \<gamma>, \<theta>, def, \<tau>)" and "P tw" and
      ex: "init' t \<sigma> \<gamma> \<theta> def (process sl : ss) \<tau> \<tau>'" and "worldline2 t \<sigma> \<theta> def \<tau>' = tw'"
      by (smt world_init_exec_cases(1))
    have "fst tw = t"
      by (metis (no_types, lifting) des destruct_worldline_def fst_conv)
    have "nonneg_delay ss"
      using SingleI by auto
    have "tw, ss \<Rightarrow>\<^sub>s tw'"
      using des \<open>worldline2 t \<sigma> \<theta> def \<tau>' = tw'\<close> ex world_seq_exec.intros by blast
    hence "Q tw'"
      using soundness_hoare2[OF SingleI(1) `nonneg_delay ss`] `P tw` `fst tw = t`
      unfolding seq_hoare_valid2_def by blast }
  then show ?case
    unfolding init_hoare_valid_def by auto
next
  case (ParallelI P cs\<^sub>1 R cs\<^sub>2 Q)
  hence "conc_stmt_wf cs\<^sub>1" and "conc_stmt_wf cs\<^sub>2"
    by (simp add: conc_stmt_wf_def)+
  moreover have "nonneg_delay_conc cs\<^sub>1" and "nonneg_delay_conc cs\<^sub>2"
    using ParallelI by auto
  ultimately have " \<Turnstile>\<^sub>I \<lbrace>P\<rbrace> cs\<^sub>1 \<lbrace>R\<rbrace>" and " \<Turnstile>\<^sub>I \<lbrace>R\<rbrace> cs\<^sub>2 \<lbrace>Q\<rbrace>"
    using ParallelI by blast+
  then show ?case
    using parallelI_valid ParallelI by blast
next
  case (ParallelI2 P cs\<^sub>2 R cs\<^sub>1 Q)
  hence "conc_stmt_wf cs\<^sub>1" and "conc_stmt_wf cs\<^sub>2"
    by (simp add: conc_stmt_wf_def)+
  moreover have "nonneg_delay_conc cs\<^sub>1" and "nonneg_delay_conc cs\<^sub>2"
    using ParallelI2 by auto
  ultimately have cs2: " \<Turnstile>\<^sub>I \<lbrace>P\<rbrace> cs\<^sub>2 \<lbrace>R\<rbrace>" and cs1: " \<Turnstile>\<^sub>I \<lbrace>R\<rbrace> cs\<^sub>1 \<lbrace>Q\<rbrace>"
    using ParallelI2 by blast+
  have "conc_stmt_wf (cs\<^sub>2 || cs\<^sub>1)"
    using ParallelI2(3) unfolding conc_stmt_wf_def by auto
  moreover have " nonneg_delay_conc (cs\<^sub>2 || cs\<^sub>1) "
    using ParallelI2(7) by auto
  ultimately have "\<Turnstile>\<^sub>I \<lbrace>P\<rbrace> cs\<^sub>2 || cs\<^sub>1 \<lbrace>Q\<rbrace>"
    using parallelI_valid[OF cs2 cs1]   by auto
  thus ?case
    using world_init_exec_commute
    by (smt ParallelI2.hyps(3) init_hoare_valid_def parallelI_comp_commute' world_init_exec.intros
    world_init_exec_cases(2))
next
  case (ConseqI P' P c Q Q')
  then show ?case  by (smt init_hoare_valid_def)
next
  case (ConjI P cs Q1 Q2)
  hence "\<Turnstile>\<^sub>I \<lbrace>P\<rbrace> cs \<lbrace>Q1\<rbrace>" and "\<Turnstile>\<^sub>I \<lbrace>P\<rbrace> cs \<lbrace>Q2\<rbrace>"
    by blast+
  then show ?case
    unfolding init_hoare_valid_def by blast
qed

inductive init_sim :: "nat \<times> 'signal worldline_init \<Rightarrow> 'signal conc_stmt \<Rightarrow> nat \<times> 'signal worldline_init \<Rightarrow> bool" where
  "     world_init_exec tw cs tw'
   \<Longrightarrow>  init_sim tw cs (next_time_world tw', snd tw')"

inductive_cases init_sim_cases [elim!]: "init_sim tw cs tw'"

definition init_sim_valid :: "'signal assn2 \<Rightarrow> 'signal conc_stmt \<Rightarrow> 'signal assn2 \<Rightarrow> bool" where
  "init_sim_valid P cs Q = (\<forall>tw tw'. P tw \<and> init_sim tw cs tw' \<longrightarrow> Q tw')"

inductive
  init_sim_hoare :: "'signal assn2 \<Rightarrow> 'signal conc_stmt \<Rightarrow> 'signal assn2 \<Rightarrow> bool" where
AssignI: "\<turnstile>\<^sub>I \<lbrace>P\<rbrace> cs \<lbrace>\<lambda>tw. Q (next_time_world tw, snd tw)\<rbrace>  \<Longrightarrow> init_sim_hoare P cs Q" |
ConseqI_sim: "\<forall>tw. P' tw \<longrightarrow> P tw \<Longrightarrow> init_sim_hoare P cs Q \<Longrightarrow> \<forall>tw. Q tw \<longrightarrow> Q' tw \<Longrightarrow> init_sim_hoare P' cs Q'" |
ConjI_sim: "init_sim_hoare P cs Q1 \<Longrightarrow> init_sim_hoare P cs Q2 \<Longrightarrow> init_sim_hoare P cs (\<lambda>tw. Q1 tw \<and> Q2 tw)"

lemma  strengthen_precondition_init_sim_hoare:
  assumes "\<forall>w. P' w \<longrightarrow> P w" and "init_sim_hoare P s Q"
  shows "init_sim_hoare P' s Q"
  using assms by (blast intro: ConseqI_sim)

lemma init_sim_hoare_soundness:
  assumes "init_sim_hoare P cs Q"
  assumes "conc_stmt_wf cs" and "nonneg_delay_conc cs"
  shows "init_sim_valid P cs Q"
  using assms
proof (induction rule:init_sim_hoare.induct)
  case (AssignI P cs Q)
  have *: "\<Turnstile>\<^sub>I \<lbrace>P\<rbrace> cs \<lbrace>\<lambda>tw. Q (next_time_world tw, snd tw)\<rbrace>"
    using soundness_init_hoare[OF AssignI] by auto
  { fix tw tw'
    assume "P tw"
    assume "tw, cs \<Rightarrow>\<^sub>I tw'"
    hence "Q (next_time_world tw', snd tw')" (is ?imp1)
      using * \<open>P tw\<close> unfolding init_hoare_valid_def by blast
    have "init_sim tw cs (next_time_world tw', snd tw')" (is ?imp2)
      using \<open>tw, cs \<Rightarrow>\<^sub>I tw'\<close>  by (simp add: init_sim.intros)
    hence "?imp1 \<and> ?imp2"
      using \<open>?imp1\<close> by auto }
  then show ?case
    unfolding init_sim_valid_def by blast
next
  case (ConseqI_sim P' P cs Q Q')
  then show ?case
    by (smt init_sim_valid_def)
next
  case (ConjI_sim P cs Q1 Q2)
  then show ?case  by (simp add: init_sim_valid_def)
qed

subsection \<open>Complete simulation = @{term "init_sim"} + @{term "world_sim_fin"}\<close>

inductive sim_fin :: "'signal worldline_init \<Rightarrow> nat \<Rightarrow> 'signal conc_stmt \<Rightarrow> nat \<times> 'signal worldline_init \<Rightarrow> bool"
  where
  "init_sim (0, w) cs tw  \<Longrightarrow> tw, T, cs \<Rightarrow>\<^sub>S tw' \<Longrightarrow> sim_fin w T cs tw'"

inductive_cases sim_fin_ic: "sim_fin w T cs tw'"

lemma premises_sim_fin:
  assumes "sim_fin w T cs tw'"
  shows "\<exists>tw. init_sim (0, w) cs tw \<and> tw, T, cs \<Rightarrow>\<^sub>S tw'"
  using sim_fin_ic[OF assms(1)]  by metis

lemma premises_sim_fin_obt:
  assumes "sim_fin w T cs tw'"
  obtains tw where "init_sim (0, w) cs tw" and "tw, T, cs \<Rightarrow>\<^sub>S tw'"
  using premises_sim_fin[OF assms] by metis

subsection \<open>The notion of typing for a worldline\<close>

definition wtyping :: "'a tyenv \<Rightarrow> 'a worldline \<Rightarrow> bool" where
  "wtyping \<Gamma> w \<equiv> (\<forall>s t. type_of (w s t) = \<Gamma> s)"

definition wityping :: "'a tyenv \<Rightarrow> 'a worldline_init \<Rightarrow> bool" where
  "wityping \<Gamma> wi \<equiv> styping \<Gamma> (fst wi) \<and> wtyping \<Gamma> (snd wi)"

lemma wityping_ensure_styping:
  "wityping \<Gamma> wi \<Longrightarrow> styping \<Gamma> (state_of_world wi t)"
  by (simp add: state_of_world_def styping_def wityping_def wtyping_def)

lemma wityping_ensure_ttyping:
  "wityping \<Gamma> wi \<Longrightarrow> ttyping \<Gamma> (derivative_hist_raw wi t)"
  by (simp add: derivative_hist_raw_def difference_raw_alt_def domIff wityping_def ttyping_def wtyping_def)

lemma worldline_upd_preserve_wityping:
  assumes "wityping \<Gamma> wi"
  assumes "type_of v = \<Gamma> sig"
  shows   "wityping \<Gamma> (wi[ sig, t := v])"
  using assms  by (simp add: wityping_def worldline_upd_def wtyping_def)

lemma worldline_inert_upd_preserve_wityping:
  assumes "wityping \<Gamma> wi"
  assumes "type_of v = \<Gamma> sig"
  shows   "wityping \<Gamma> (wi[ sig, t, dly := v])"
  using assms unfolding wityping_def worldline_inert_upd_def wtyping_def by simp

lemma seq_stmt_preserve_wityping_hoare:
  assumes "seq_wt \<Gamma> ss"
  shows " \<turnstile> [\<lambda>tw. wityping \<Gamma> (snd tw) ] ss [\<lambda>tw. wityping \<Gamma> (snd tw)]"
  using assms
proof (induction rule:seq_wt.inducts)
  case (1 \<Gamma>)
  then show ?case by (intro Null2)
next
  case (2 \<Gamma> s1 s2)
  then show ?case by (auto)
next
  case (3 \<Gamma> g s1 s2)
  then show ?case
    by (intro If2) (rule strengthen_precondition, simp)+
next
  case (4 \<Gamma> exp sig dly)
  hence "\<forall>tw x.   wityping \<Gamma> (snd tw) \<and> beval_world_raw2 tw exp x \<longrightarrow> type_of x = \<Gamma> sig"
    by (metis beval_raw_preserve_well_typedness beval_world_raw2_def beval_world_raw_cases
    wityping_def wityping_ensure_styping wityping_ensure_ttyping)
  then show ?case
    by (intro Assign2_altI)
       (simp add: worldline_upd_preserve_wityping worldline_upd2_def)
next
  case (5 \<Gamma> exp sig dly)
  hence "\<forall>tw x.   wityping \<Gamma> (snd tw) \<and> beval_world_raw2 tw exp x \<longrightarrow> type_of x = \<Gamma> sig"
    by (metis beval_raw_preserve_well_typedness beval_world_raw2_def beval_world_raw_cases
    wityping_def wityping_ensure_styping wityping_ensure_ttyping)
  then show ?case
    by (intro AssignI2_altI)
       (simp add: worldline_inert_upd_preserve_wityping worldline_inert_upd2_def)
next
  case (6 \<Gamma> exp ty)
  then show ?case by simp
next
  case (7 \<Gamma> exp ty ss choices)
  then show ?case by blast
next
  case (8 \<Gamma> exp ty exp' ss choices)
  then show ?case
    by (simp add: strengthen_precondition)
qed

lemma single_conc_stmt_preserve_wityping_hoare:
  assumes "seq_wt \<Gamma> ss"
  shows " \<turnstile> \<lbrace>\<lambda>tw. wityping \<Gamma> (snd tw) \<rbrace> process sl : ss \<lbrace>\<lambda>tw. wityping \<Gamma> (snd tw)\<rbrace>"
  apply (intro Single)
   apply (rule strengthen_precondition)
   apply (rule seq_stmt_preserve_wityping_hoare)
  using assms conc_wt.cases apply fastforce
  by blast

lemma single_conc_stmt_preserve_wityping_init_hoare:
  assumes "seq_wt \<Gamma> ss"
  shows "\<turnstile>\<^sub>I \<lbrace>\<lambda>tw. wityping \<Gamma> (snd tw)\<rbrace>  process sl : ss \<lbrace>\<lambda>tw. wityping \<Gamma> (snd tw)\<rbrace>"
  apply (intro SingleI)
  apply (rule seq_stmt_preserve_wityping_hoare)
  using assms conc_wt.cases apply fastforce
  done

lemma single_conc_stmt_preserve_wityping_init_sim_hoare:
  assumes "seq_wt \<Gamma> ss"
  shows "init_sim_hoare (\<lambda>tw. wityping \<Gamma> (snd tw)) (process sl : ss) (\<lambda>tw. wityping \<Gamma> (snd tw))"
  apply (intro AssignI)
  unfolding snd_conv apply (rule single_conc_stmt_preserve_wityping_init_hoare)
  apply (rule assms)
  done

end