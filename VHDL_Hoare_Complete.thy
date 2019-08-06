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
  "nat \<times> 'signal worldline \<Rightarrow> 'signal \<Rightarrow> nat \<Rightarrow> val \<Rightarrow> nat \<times> 'signal worldline" ("_[ _, _ :=\<^sub>2 _]")
  where "worldline_upd2 \<equiv> \<lambda>tw sig dly val. (fst tw, worldline_upd (snd tw) sig (fst tw + dly) val)"

lemma worldline_upd2_before_dly:
  fixes tw val dly sig
  defines "tw' \<equiv> tw[sig, dly :=\<^sub>2 val]"
  shows "\<And>s i. i < fst tw + dly \<Longrightarrow> snd tw' s i = snd tw s i"
  unfolding tw'_def worldline_upd2_def worldline_upd_def by auto

lemma worldline_upd2_at_dly:
  fixes tw val dly sig
  defines "tw' \<equiv> tw[sig, dly :=\<^sub>2 val]"
  shows "snd tw' sig (fst tw + dly) = val"
  unfolding tw'_def worldline_upd2_def worldline_upd_def by auto

lemma worldline_upd2_at_dly_nonsig:
  fixes tw val dly sig
  defines "tw' \<equiv> tw[sig, dly :=\<^sub>2 val]"
  shows "s \<noteq> sig \<Longrightarrow> snd tw' s (fst tw + dly) = snd tw s (fst tw + dly)"
  unfolding tw'_def worldline_upd2_def worldline_upd_def by auto
  
definition worldline_inert_upd2 ::
  "nat \<times> 'signal worldline \<Rightarrow> 'signal \<Rightarrow> nat \<Rightarrow> val \<Rightarrow> nat \<times> 'signal worldline" ("_\<lbrakk> _, _ :=\<^sub>2 _\<rbrakk>")
  where "worldline_inert_upd2 \<equiv> \<lambda>tw sig dly v. (fst tw, worldline_inert_upd (snd tw) sig (fst tw) dly v)"

definition beval_world_raw2 :: "nat \<times> 'signal worldline \<Rightarrow> 'signal bexp \<Rightarrow> val" where 
  "beval_world_raw2 \<equiv> \<lambda>tw exp. beval_world_raw (snd tw) (fst tw) exp" 

lemma beval_world_raw2_Bsig:
  "beval_world_raw2 tw (Bsig s) = snd tw s (fst tw)"
  unfolding beval_world_raw2_def beval_world_raw_def state_of_world_def by auto

type_synonym 'signal assn2 = "nat \<times> 'signal worldline \<Rightarrow> bool"

inductive
  seq_hoare2 :: "'signal assn2 \<Rightarrow> 'signal seq_stmt \<Rightarrow> 'signal assn2 \<Rightarrow> bool" ("\<turnstile> ([(1_)]/ (_)/ [(1_)])" 50)
  where
Null2: "\<turnstile> [P] Bnull [P]" |
Assign2: "\<turnstile> [\<lambda>tw. P(  tw[sig, dly :=\<^sub>2 beval_world_raw2 tw exp] )] Bassign_trans sig exp dly [P]" |

AssignI2: "\<turnstile> [\<lambda>tw. P( tw\<lbrakk>sig, dly :=\<^sub>2 (beval_world_raw2 tw exp)\<rbrakk>  )] Bassign_inert sig exp dly [P]" |

Comp2: "\<lbrakk> \<turnstile> [P] s1 [Q]; \<turnstile> [Q] s2 [R]\<rbrakk> \<Longrightarrow> \<turnstile> [P] Bcomp s1 s2 [R]" |

If2: "\<lbrakk>\<turnstile> [\<lambda>tw. P tw \<and> beval_world_raw2 tw g] s1 [Q]; \<turnstile> [\<lambda>tw. P tw \<and> \<not> beval_world_raw2 tw g] s2 [Q]\<rbrakk>
        \<Longrightarrow>  \<turnstile> [P] Bguarded g s1 s2 [Q]" |

Conseq2: "\<lbrakk>\<forall>tw. P' tw \<longrightarrow> P tw; \<turnstile> [P] s [Q]; \<forall>tw. Q tw \<longrightarrow> Q' tw\<rbrakk> \<Longrightarrow> \<turnstile> [P'] s [Q']" | 

Conj: "\<turnstile> [P] s [Q1] \<Longrightarrow> \<turnstile> [P] s [Q2] \<Longrightarrow> \<turnstile> [P] s [\<lambda>tw. Q1 tw \<and> Q2 tw]"

text \<open>Derived rules\<close>

lemma strengthen_precondition:
  "\<turnstile> [P] ss [Q] \<Longrightarrow> \<turnstile> [\<lambda>tw. P tw \<and> P' tw] ss [Q]"
  by (rule Conseq2[where Q="Q" and P="P"]) auto

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
  "\<forall>tw. P tw \<longrightarrow> Q(tw[sig, dly :=\<^sub>2 beval_world_raw2 tw exp]) \<Longrightarrow> \<turnstile> [P] Bassign_trans sig exp dly [Q]"
  apply (rule Conseq2[where Q="Q", rotated 1])
    apply (rule Assign2)
   apply simp
  apply simp
  done

lemma AssignI2_altI:
  "\<forall>tw. P tw \<longrightarrow> Q(tw\<lbrakk>sig, dly :=\<^sub>2 beval_world_raw2 tw exp\<rbrakk>) \<Longrightarrow> \<turnstile> [P] Bassign_inert sig exp dly [Q]"
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
  shows "\<forall>tw. P tw \<longrightarrow> Q(tw[sig, dly :=\<^sub>2 beval_world_raw2 tw exp])"
  using assms
proof (induction rule: seq_hoare2.induct)
  case (Conseq2 P' P s Q Q')
  then show ?case by blast
qed auto


lemma Bassign_inertE_hoare2:
  assumes "\<turnstile> [P] s [Q]"
  assumes "s = Bassign_inert sig exp dly"
  shows "\<forall>tw. P tw \<longrightarrow> Q(tw \<lbrakk> sig, dly :=\<^sub>2 beval_world_raw2 tw exp\<rbrakk> )"
  using assms
proof (induction rule: seq_hoare2.induct)
  case (Conseq2 P' P s Q Q')
  then show ?case by blast
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
lemmas [intro!] = seq_hoare2.Null2 seq_hoare2.Assign2 seq_hoare2.Comp2 seq_hoare2.If2

lemma strengthen_pre_hoare2:
  assumes "\<forall>tw. P' tw \<longrightarrow> P tw" and "\<turnstile> [P] s [Q]"
  shows "\<turnstile> [P'] s [Q]"
  using assms by (blast intro: Conseq2)

lemma weaken_post_hoare2:
  assumes "\<forall>tw. Q tw \<longrightarrow> Q' tw" and "\<turnstile> [P] s [Q]"
  shows "\<turnstile> [P] s [Q']"
  using assms by (blast intro: Conseq2)

lemma Assign'_hoare2:
  assumes "\<forall>tw. P tw \<longrightarrow> Q (worldline_upd2 tw sig dly (beval_world_raw2 tw exp))"
  shows "\<turnstile> [P] Bassign_trans sig exp dly [Q]"
  using assms by (metis (no_types, lifting) Assign2 strengthen_pre_hoare2)

subsubsection \<open>Validity of Hoare proof rules\<close>

definition worldline2 ::
  "nat \<Rightarrow> 'signal state \<Rightarrow> 'signal trans_raw \<Rightarrow> 'signal trans_raw \<Rightarrow> nat \<times> 'signal worldline"
  where "worldline2 \<equiv> \<lambda>t \<sigma> \<theta> \<tau>. (t, worldline_raw t \<sigma> \<theta> \<tau>)"

definition destruct_worldline ::
  "nat \<times> 'signal worldline \<Rightarrow> (nat \<times> 'signal state \<times> 'signal event \<times> 'signal trans_raw \<times> 'signal trans_raw)"
  where
  "destruct_worldline tw = (let  t = fst tw; w = snd tw;
                                 \<sigma> = (\<lambda>s. w s t);
                                 \<theta> = derivative_hist_raw w t;
                                 \<gamma> = {s. \<sigma> s \<noteq> signal_of False \<theta> s (t - 1)};
                                 \<tau> = derivative_raw w t
                             in (t, \<sigma>, \<gamma>, \<theta>, \<tau>))"

lemma destruct_worldline_trans_zero_upto_now:
  assumes "destruct_worldline tw = (t, \<sigma>, \<gamma>, \<theta>, \<tau>)"
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
@{term "signal_of False \<theta> s (t - 1)"} is equal to @{term "signal_of False 0 s 0"} and,
subsequently, equals to @{term "False"}. Hence, when @{term "t = 0"}, the @{term "\<gamma>"} enumerates the
signals which are different with the default value @{term "False :: val"}.\<close>

lemma destruct_worldline_no_trans_at_t:
  "destruct_worldline tw = (t, \<sigma>, \<gamma>, \<theta>, \<tau>) \<Longrightarrow> \<tau> t = 0"
proof -
  assume "destruct_worldline tw = (t, \<sigma>, \<gamma>, \<theta>, \<tau>)"
  hence "\<tau> = derivative_raw (snd tw) (fst tw)" and "fst tw = t"
    unfolding destruct_worldline_def Let_def by auto
  thus ?thesis
    by (auto simp add: derivative_raw_def zero_fun_def zero_option_def)
qed

lemma fst_destruct_worldline:
  "fst (destruct_worldline tw) = fst tw"
  unfolding destruct_worldline_def Let_def by auto

lemma destruct_worldline_exist:
  "\<exists>t \<sigma> \<gamma> \<theta> \<tau>. destruct_worldline tw = (t, \<sigma>, \<gamma>, \<theta>, \<tau>)"
  unfolding destruct_worldline_def Let_def by auto

lemma worldline2_constructible:
  fixes tw :: "nat \<times> 'signal worldline"
  assumes "destruct_worldline tw = (t, \<sigma>, \<gamma>, \<theta>, \<tau>)"
  shows "tw = worldline2 t \<sigma> \<theta> \<tau> \<and> context_invariant t \<sigma> \<gamma> \<theta> \<tau>"
proof -
  let ?w = "snd tw"
  have **:
      "(fst tw,
        \<lambda>s. snd tw s (fst tw),
        {s. snd tw s (fst tw) \<noteq> signal_of False (derivative_hist_raw (snd tw) (fst tw)) s (fst tw - 1)},
        derivative_hist_raw (snd tw) (fst tw),
        derivative_raw (snd tw) (fst tw)) =
        (t, \<sigma>, \<gamma>, \<theta>, \<tau>)"
    using assms unfolding destruct_worldline_def Let_def by auto
  hence \<sigma>_def: "\<sigma> = (\<lambda>s. ?w s t)" and
        \<gamma>_def: "\<gamma> = {s. ?w s t \<noteq> signal_of False (derivative_hist_raw (snd tw) (fst tw)) s (fst tw - 1)}" and
        \<theta>_def: "\<theta> = derivative_hist_raw ?w t" and
        "fst tw = t"
    by auto
  have \<tau>_def: "\<tau> = derivative_raw ?w t"
    using ** by auto
  have "?w = worldline_raw t \<sigma> \<theta> \<tau>"
  proof (rule ext, rule ext)
    fix s' t'
    have "snd tw s' t = \<sigma> s'"
      unfolding \<sigma>_def by auto
    have "t' < t \<or> t \<le> t'" by auto
    moreover
    { assume "t' < t"
      hence "worldline_raw t \<sigma> \<theta> \<tau> s' t' =  signal_of False \<theta> s' t'"
        unfolding worldline_raw_def by auto
      also have "... = ?w s' t'"
        using signal_of_derivative_hist_raw[OF `t' < t`] unfolding \<theta>_def  by metis
      finally have "?w s' t' = worldline_raw t \<sigma> \<theta> \<tau> s' t'"
        by auto }
    moreover
    { assume "t \<le> t'"
      hence "worldline_raw t \<sigma> \<theta> \<tau> s' t' = signal_of (\<sigma> s') \<tau> s' t'"
        unfolding worldline_raw_def by auto
      also have "... = ?w s' t'"
        unfolding \<tau>_def using `snd tw s' t = \<sigma> s'` by (metis \<open>t \<le> t'\<close> signal_of_derivative_raw)
      finally have "?w s' t' = worldline_raw t \<sigma> \<theta> \<tau> s' t'"
        by auto }
    ultimately show "?w s' t' = worldline_raw t \<sigma> \<theta> \<tau> s' t'"
      by auto
  qed
  have "\<forall>n. t \<le> n \<longrightarrow> \<theta> n = 0"
    unfolding \<theta>_def by (auto simp add: derivative_hist_raw_def zero_fun_def zero_option_def)
  moreover have "\<forall>n. n \<le> t \<longrightarrow> \<tau> n = 0"
    unfolding \<tau>_def by (auto simp add: derivative_raw_def zero_fun_def zero_option_def)
  ultimately have "context_invariant t \<sigma> \<gamma> \<theta> \<tau>"
    unfolding \<gamma>_def context_invariant_def \<sigma>_def \<theta>_def `fst tw = t` by auto
  thus "  tw = worldline2 t \<sigma> \<theta> \<tau> \<and> context_invariant t \<sigma> \<gamma> \<theta> \<tau>"
    using `?w = worldline_raw t \<sigma> \<theta> \<tau>` `fst tw = t` surjective_pairing[of "tw"] 
    by (metis worldline2_def)
qed

lemma worldline2_constructible':
  fixes tw :: "nat \<times> 'signal worldline"
  shows "\<exists>t \<sigma> \<gamma> \<theta> \<tau>. tw = worldline2 t \<sigma> \<theta> \<tau> \<and> context_invariant t \<sigma> \<gamma> \<theta> \<tau>"
  using destruct_worldline_exist worldline2_constructible by blast

lemma state_worldline2:
  assumes "\<forall>n. n \<le> t \<longrightarrow>  \<tau> n = 0"
  assumes "\<forall>n. t \<le> n \<longrightarrow>  \<theta> n = 0"
  shows "(\<lambda>s. snd (worldline2 t \<sigma> \<theta> \<tau>) s t) = \<sigma>"
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
  hence "worldline_raw t \<sigma> \<theta> \<tau> s t = \<sigma> s"
    unfolding worldline_raw_def by auto
  thus "snd (worldline2 t \<sigma> \<theta> \<tau>) s t = \<sigma> s"
    by (simp add: worldline2_def)
qed

lemma hist_of_worldline:
  assumes "\<forall>n. n \<le> t \<longrightarrow>  \<tau> n = 0"
  assumes "\<forall>n. t \<le> n \<longrightarrow>  \<theta> n = 0"  
  shows "\<And>k. signal_of False (derivative_hist_raw (snd (worldline2 t \<sigma> \<theta> \<tau>)) t) s k = signal_of False \<theta> s k"
  using assms
proof -
  fix k 
  have *: "signal_of False (derivative_hist_raw (snd (worldline2 t \<sigma> \<theta> \<tau>)) t) s k  =
           signal_of False (derivative_hist_raw (worldline_raw t \<sigma> \<theta> \<tau>) t) s k" 
    unfolding worldline2_def by auto
  have "\<theta> t = 0"
    using assms by auto
  have "k < t \<or> t \<le> k"
    by auto
  moreover
  { assume "k < t"
    have "signal_of False (derivative_hist_raw (worldline_raw t \<sigma> \<theta> \<tau>) t) s k = worldline_raw t \<sigma> \<theta> \<tau> s k"
      using signal_of_derivative_hist_raw[OF `k < t`] by metis
    also have "... = signal_of False \<theta> s k"
      using `k < t` unfolding worldline_raw_def by auto
    finally have "signal_of False (derivative_hist_raw (snd (worldline2 t \<sigma> \<theta> \<tau>)) t) s k  = signal_of False \<theta> s k "
      using * by auto }
  moreover
  { assume "t \<le> k"
    hence "t < k \<or> t = k" by auto
    moreover
    { assume "t < k"
      moreover have "\<And>n. t < n \<Longrightarrow> n \<le> k \<Longrightarrow> (derivative_hist_raw (worldline_raw t \<sigma> \<theta> \<tau>) t) n s = None"
        by (auto simp add: derivative_hist_raw_def)
      ultimately have "signal_of False (derivative_hist_raw (worldline_raw t \<sigma> \<theta> \<tau>) t) s k =
                       signal_of False (derivative_hist_raw (worldline_raw t \<sigma> \<theta> \<tau>) t) s t"
        by (intro signal_of_less_ind')( auto simp add: zero_option_def) }
    moreover
    { assume "t = k"
      hence "signal_of False (derivative_hist_raw (worldline_raw t \<sigma> \<theta> \<tau>) t) s k =
             signal_of False (derivative_hist_raw (worldline_raw t \<sigma> \<theta> \<tau>) t) s t"
        by auto }
    ultimately have **: "signal_of False (derivative_hist_raw (worldline_raw t \<sigma> \<theta> \<tau>) t) s k =
                         signal_of False (derivative_hist_raw (worldline_raw t \<sigma> \<theta> \<tau>) t) s t" by auto
    have "(derivative_hist_raw (worldline_raw t \<sigma> \<theta> \<tau>) t) t = Map.empty"
      by (auto simp add: derivative_hist_raw_def)
    hence ***: "signal_of False (derivative_hist_raw (worldline_raw t \<sigma> \<theta> \<tau>) t) s t =
                signal_of False (derivative_hist_raw (worldline_raw t \<sigma> \<theta> \<tau>) t) s (t - 1)"
      using signal_of_less_sig zero_option_def  by metis
    have "0 < t \<or> t = 0"
      by auto
    moreover
    { assume "0 < t"
      hence "t - 1 < t"
        by linarith
      hence "signal_of False (derivative_hist_raw (worldline_raw t \<sigma> \<theta> \<tau>) t) s (t - 1) = worldline_raw t \<sigma> \<theta> \<tau> s (t - 1)"
        using signal_of_derivative_hist_raw[of "t-1" "t"] by metis
      also have "... = signal_of False \<theta> s (t- 1)"
        using `t- 1 < t`unfolding worldline_raw_def by auto
      also have "... = signal_of False \<theta> s t"
        using signal_of_less[where \<tau>="\<theta>", OF `\<theta> t = 0`] by auto
      also have "... = signal_of False \<theta> s k"
        by (metis \<open>\<forall>n\<ge>t. \<theta> n = 0\<close> \<open>t < k \<or> t = k\<close> order.strict_implies_order signal_of_less_ind)
      finally have "signal_of False (derivative_hist_raw (worldline_raw t \<sigma> \<theta> \<tau>) t) s (t - 1) = signal_of False \<theta> s k"
        by auto
      hence "signal_of False (derivative_hist_raw (snd (worldline2 t \<sigma> \<theta> \<tau>)) t) s k  = signal_of False \<theta> s k"
        using * ** *** by blast } 
    moreover
    { assume "t = 0"             
      have  "(derivative_hist_raw (worldline_raw t \<sigma> \<theta> \<tau>) t) t = Map.empty"
        unfolding `t = 0` by (auto simp add: derivative_hist_raw_def)
      hence "signal_of False (derivative_hist_raw (worldline_raw t \<sigma> \<theta> \<tau>) t) s t =  False"
        using signal_of_zero unfolding `t = 0` by (metis zero_option_def)
      also have "... = signal_of False \<theta> s 0"
        using `\<theta> t = 0` unfolding `t = 0` using signal_of_zero by (metis zero_fun_def)
      also have "... = signal_of False \<theta> s k"
        by (metis \<open>\<forall>n\<ge>t. \<theta> n = 0\<close> \<open>t < k \<or> t = k\<close> \<open>t = 0\<close> le0 signal_of_less_ind)
      finally have "signal_of False (derivative_hist_raw (worldline_raw t \<sigma> \<theta> \<tau>) t) s t = signal_of False \<theta> s k"
        by auto
      hence "signal_of False (derivative_hist_raw (snd (worldline2 t \<sigma> \<theta> \<tau>)) t) s k   = signal_of False \<theta> s k"
        using * ** by auto }
    ultimately have "signal_of False (derivative_hist_raw (snd (worldline2 t \<sigma> \<theta> \<tau>)) t) s k   = signal_of False \<theta> s k"
      by auto }
  ultimately show "signal_of False (derivative_hist_raw (snd (worldline2 t \<sigma> \<theta> \<tau>)) t) s k   = signal_of False \<theta> s k"
    by auto
qed

lemma event_worldline2':
  assumes "context_invariant t \<sigma> \<gamma> \<theta> \<tau>"
  shows "{s. snd (worldline2 t \<sigma> \<theta> \<tau>) s t \<noteq> signal_of False  (derivative_hist_raw (snd (worldline2 t \<sigma> \<theta> \<tau>)) t) s (t - 1)} = \<gamma>"
proof -
  have "\<forall>n\<le>t. \<tau> n = 0" and "\<forall>n. t \<le> n \<longrightarrow>  \<theta> n = 0"
    using assms unfolding context_invariant_def by auto
  hence *: "(\<lambda>s. snd (worldline2 t \<sigma> \<theta> \<tau>) s t) = \<sigma>"
    by (intro state_worldline2)  
  have **: "\<gamma> = {s. \<sigma> s \<noteq> signal_of False \<theta> s (t - 1)}"
    using `context_invariant t \<sigma> \<gamma> \<theta> \<tau>` unfolding context_invariant_def by auto
  have "{s. worldline_raw t \<sigma> \<theta> \<tau> s t \<noteq> signal_of False (derivative_hist_raw (worldline_raw t \<sigma> \<theta> \<tau>) t) s (t - 1)} =
        {s. \<sigma> s \<noteq> signal_of False (derivative_hist_raw (worldline_raw t \<sigma> \<theta> \<tau>) t) s (t - 1)}"
    by (metis (no_types) "*" prod.sel(2) worldline2_def)
  moreover have "\<And>s. signal_of False \<theta> s (t - 1) =
                      signal_of False (derivative_hist_raw (worldline_raw t \<sigma> \<theta> \<tau>) t) s (t - 1)"
    using hist_of_worldline 
    by (metis (full_types) \<open>\<forall>n\<ge>t. \<theta> n = 0\<close> \<open>\<forall>n\<le>t. \<tau> n = 0\<close> prod.sel(2) worldline2_def)
  ultimately have "{s. worldline_raw t \<sigma> \<theta> \<tau> s t \<noteq> signal_of False (derivative_hist_raw (worldline_raw t \<sigma> \<theta> \<tau>) t) s (t - 1)} =
                   {s. \<sigma> s \<noteq> signal_of False \<theta> s (t - 1)}"
    by auto
  thus ?thesis
    using **  by (simp add: worldline2_def)
qed

lemma transaction_worldline2:
  assumes "\<forall>n. n \<le> t \<longrightarrow>  \<tau> n = 0"
  assumes "\<forall>n. t \<le> n \<longrightarrow>  \<theta> n = 0"
  shows "\<And>k s . signal_of (\<sigma> s) (derivative_raw (snd (worldline2 t \<sigma> \<theta> \<tau>)) t) s k = signal_of (\<sigma> s) \<tau> s k"
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
  hence "worldline_raw t \<sigma> \<theta> \<tau> s t = \<sigma> s"
    by (simp add: worldline_raw_def)
  have "k < t \<or> t \<le> k"
    by auto
  moreover
  { assume "k < t"
    have "signal_of (\<sigma> s) (derivative_raw (worldline_raw t \<sigma> \<theta> \<tau>) t) s k = \<sigma> s"
      using signal_of2_derivative_before_now \<open>k < t\<close> by fastforce
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
    ultimately have "signal_of (\<sigma> s) (derivative_raw (worldline_raw t \<sigma> \<theta> \<tau>) t) s k =
                     signal_of (\<sigma> s) \<tau> s k"
      by auto }
  moreover
  { assume "t \<le> k"
    hence "signal_of (\<sigma> s) (derivative_raw (worldline_raw t \<sigma> \<theta> \<tau>)  t) s k = (worldline_raw t \<sigma> \<theta> \<tau>) s k"
      using signal_of_derivative_raw `worldline_raw t \<sigma> \<theta> \<tau> s t = \<sigma> s` by metis
    also have "... = signal_of (\<sigma> s) \<tau> s k"
      unfolding worldline_raw_def using `t \<le> k` by auto
    finally have "signal_of (\<sigma> s) (derivative_raw (worldline_raw t \<sigma> \<theta> \<tau>)  t) s k =
                  signal_of (\<sigma> s) \<tau> s k"
      by auto }
  ultimately have "signal_of (\<sigma> s) (derivative_raw (worldline_raw t \<sigma> \<theta> \<tau>) t) s k =
                    signal_of (\<sigma> s) \<tau> s k" by auto
  thus "signal_of (\<sigma> s) (derivative_raw (snd (worldline2 t \<sigma> \<theta> \<tau>)) t) s k = signal_of (\<sigma> s) \<tau> s k"
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
  assumes "\<forall>n. t \<le> n \<longrightarrow>  \<theta> n = 0"
  assumes "\<forall>s. non_stuttering (to_trans_raw_sig \<tau>) \<sigma> s"
  shows "derivative_raw (snd (worldline2 t \<sigma> \<theta> \<tau>)) t = \<tau>"
  using assms unfolding worldline2_def 
  by (simp add: derivative_raw_of_worldline_specific)

lemma derivative_is_history2:
  assumes "\<forall>n. n \<le> t \<longrightarrow>  \<tau> n = 0"
  assumes "\<forall>n. t \<le> n \<longrightarrow>  \<theta> n = 0"  
  assumes "\<forall>s. non_stuttering (to_trans_raw_sig \<theta>) def_state s"
  shows "derivative_hist_raw (snd (worldline2 t \<sigma> \<theta> \<tau>)) t = \<theta>"
  using assms unfolding worldline2_def
  by (simp add: derivative_is_history)

text \<open>Several lemmas about preserving non_stuttering property.\<close>

lemma b_conc_exec_preserves_non_stuttering:
  assumes "t, \<sigma>, \<gamma>, \<theta> \<turnstile> <cs, \<tau>> \<longrightarrow>\<^sub>c \<tau>'"
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
  define \<tau>1 where "\<tau>1 = b_conc_exec t \<sigma> \<gamma> \<theta> cs1 \<tau>"
  hence "non_stuttering (to_trans_raw_sig \<tau>1) \<sigma> s"
    using Bpar(1)[OF _ Bpar(4-5)]  `nonneg_delay_conc cs1` `conc_stmt_wf cs1`
    by metis
  define \<tau>2 where "\<tau>2 = b_conc_exec t \<sigma> \<gamma> \<theta> cs2 \<tau>"
  hence "non_stuttering (to_trans_raw_sig \<tau>2) \<sigma> s"
    using Bpar(2)[OF _ Bpar(4-5)] `nonneg_delay_conc cs2` `conc_stmt_wf cs2`
    by auto
  have \<tau>'_def: "\<tau>' = clean_zip_raw \<tau> (\<tau>1, set (signals_from cs1)) (\<tau>2, set (signals_from cs2))"
    using Bpar unfolding \<tau>1_def \<tau>2_def by auto
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
  assumes "init' t \<sigma> \<gamma> \<theta> cs \<tau> = \<tau>'"
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
  define \<tau>1 where "\<tau>1 = init' t \<sigma> \<gamma> \<theta> cs1 \<tau>"
  hence "non_stuttering (to_trans_raw_sig \<tau>1) \<sigma> s"
    using Bpar(1)[OF _ Bpar(4-5)]  `nonneg_delay_conc cs1` `conc_stmt_wf cs1`
    by metis
  define \<tau>2 where "\<tau>2 = init' t \<sigma> \<gamma> \<theta> cs2 \<tau>"
  hence "non_stuttering (to_trans_raw_sig \<tau>2) \<sigma> s"
    using Bpar(2)[OF _ Bpar(4-5)] `nonneg_delay_conc cs2` `conc_stmt_wf cs2`
    by auto
  have \<tau>'_def: "\<tau>' = clean_zip_raw \<tau> (\<tau>1, set (signals_from cs1)) (\<tau>2, set (signals_from cs2))"
    using Bpar unfolding \<tau>1_def \<tau>2_def by auto
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
  "fst (worldline2 t \<sigma> \<theta> \<tau>) = t"
  unfolding worldline2_def by auto

lemma destruct_worldline_correctness:
  assumes "context_invariant t \<sigma> \<gamma> \<theta> \<tau>"
  assumes "destruct_worldline (worldline2 t \<sigma> \<theta> \<tau>) = (t', \<sigma>', \<gamma>', \<theta>', \<tau>')"
  shows "t = t'"
    and "\<sigma> = \<sigma>'"
    and "\<gamma> = \<gamma>'"
    and "\<And>k s. signal_of False \<theta> s k = signal_of False \<theta>' s k"
    and "\<And>k s. signal_of (\<sigma> s) \<tau> s k = signal_of (\<sigma> s) \<tau>' s k"
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
    Let_def by  auto
next
  have *: "\<forall>n\<le>t. \<tau> n = 0" and **: "\<forall>n\<ge>t. \<theta> n = 0"
    using assms unfolding context_invariant_def by auto
  show "\<And>k s. signal_of False \<theta> s k = signal_of False \<theta>' s k"
    using hist_of_worldline[OF * **] assms(2) unfolding destruct_worldline_def Let_def by auto
next
  have *: "\<forall>n\<le>t. \<tau> n = 0" and **: "\<forall>n\<ge>t. \<theta> n = 0"
    using assms unfolding context_invariant_def by auto
  show "\<And>k s. signal_of (\<sigma> s) \<tau> s k = signal_of (\<sigma> s) \<tau>' s k"
    using transaction_worldline2[OF * **] assms(2) unfolding destruct_worldline_def Let_def by auto
qed
  
lemma destruct_worldline_correctness2:
  assumes "context_invariant t \<sigma> \<gamma> \<theta> \<tau>"
  assumes "\<forall>s. non_stuttering (to_trans_raw_sig \<tau>) \<sigma> s"
  assumes " \<forall>s. non_stuttering (to_trans_raw_sig \<theta>) def_state s"
  assumes "destruct_worldline (worldline2 t \<sigma> \<theta> \<tau>) = (t', \<sigma>', \<gamma>', \<theta>', \<tau>')"
  shows "t = t'" and "\<sigma> = \<sigma>'" and "\<gamma> = \<gamma>'" and "\<tau> = \<tau>'" and "\<theta> = \<theta>'"
proof -
  show "t = t'" and "\<sigma> = \<sigma>'" and "\<gamma> = \<gamma>'"
    using destruct_worldline_correctness[OF assms(1) assms(4)] by auto
next
  have *: "\<forall>n\<le>t. \<tau> n = 0" and **: "\<forall>n\<ge>t. \<theta> n = 0"
    using assms unfolding context_invariant_def by auto
  show "\<tau> = \<tau>'"
    using derivative_raw_of_worldline2[OF * ** assms(2)] assms(4) unfolding destruct_worldline_def
    Let_def by auto
next
  have *: "\<forall>n\<le>t. \<tau> n = 0" and **: "\<forall>n\<ge>t. \<theta> n = 0"
    using assms unfolding context_invariant_def by auto  
  show "\<theta> = \<theta>'"
    using derivative_is_history2[OF * ** assms(3)] assms(4) unfolding destruct_worldline_def
    Let_def by auto
qed

lemma destruct_worldline_correctness3:
  assumes "context_invariant t \<sigma> \<gamma> \<theta> \<tau>"
  assumes "\<forall>s. non_stuttering (to_trans_raw_sig \<tau>) \<sigma> s"
  assumes "\<forall>s. non_stuttering (to_trans_raw_sig \<theta>) def_state s"
  shows "destruct_worldline (worldline2 t \<sigma> \<theta> \<tau>) = (t, \<sigma>, \<gamma>, \<theta>, \<tau>)"
  using destruct_worldline_correctness2[OF assms]
    by (metis (no_types, lifting) destruct_worldline_def)

definition world_seq_exec :: "nat \<times> 'signal worldline \<Rightarrow> 'signal seq_stmt \<Rightarrow> nat \<times> 'signal worldline" where
  "world_seq_exec tw s = (let (t, \<sigma>, \<gamma>, \<theta>, \<tau>) = destruct_worldline tw;
                                           \<tau>' = b_seq_exec t \<sigma> \<gamma> \<theta> s \<tau>
                           in worldline2 t \<sigma> \<theta> \<tau>')"

abbreviation world_seq_exec_abb :: "nat \<times> 'signal worldline \<Rightarrow> 'signal seq_stmt \<Rightarrow> nat \<times> 'signal worldline \<Rightarrow> bool"
  ("(_ , _) \<Rightarrow>\<^sub>s _")
  where "world_seq_exec_abb tw s tw' \<equiv> (world_seq_exec tw s = tw')"

(* Diagram for lifting the sequential execution to the worldline level
 *
 *         w, t                    \<Rightarrow>\<^sub>s          w', t
 *           \<down>                                  \<up>
 *   destruct_worldline                      worldline2 t \<sigma> \<theta> \<tau>'
 *           \<down>                                  \<up>
 *         t, \<sigma>, \<gamma>, \<theta> \<turnstile> <s, \<tau>>    \<longrightarrow>\<^sub>s          \<tau>'
 *
 *)

lemma time_invariant:
  assumes "tw, s \<Rightarrow>\<^sub>s tw'" shows "fst tw = fst tw'"
  using assms unfolding world_seq_exec_def Let_def
  by (auto dest!: worldline2_constructible split:prod.splits)

definition
seq_hoare_valid2 :: "'signal assn2 \<Rightarrow> 'signal seq_stmt \<Rightarrow> 'signal assn2 \<Rightarrow> bool" ("\<Turnstile> [(1_)]/ (_)/ [(1_)]" 50)
where "\<Turnstile> [P] s [Q] \<longleftrightarrow>  (\<forall>tw tw'.  P tw \<and> (tw, s \<Rightarrow>\<^sub>s tw') \<longrightarrow> Q tw')"

text \<open>This is a cleaner definition of the validity compared to @{term "seq_hoare_valid"} in
@{theory "Draft.VHDL_Hoare"}. This also has the same spirit as the definition of validity in
@{theory_text "Hoare"}.\<close>

lemma beval_cong:
  assumes "\<And>k s. signal_of False \<theta>1 s k = signal_of False \<theta>2 s k"
  shows "beval_raw t \<sigma> \<gamma> \<theta>1 g \<longleftrightarrow> beval_raw t \<sigma> \<gamma> \<theta>2 g"
  using assms by (induction g, auto)

lemma signal_of_eq_is_stable:
  assumes "is_stable_raw dly \<tau>1 t sig (\<sigma> sig)"
  assumes "\<And>k s. signal_of (\<sigma> s) \<tau>1 s k = signal_of (\<sigma> s) \<tau>2 s k"
  assumes "\<And>n. n \<le> t \<Longrightarrow> \<tau>1 n = 0"
  shows   "is_stable_raw dly \<tau>2 t sig (\<sigma> sig)"
  unfolding is_stable_raw_correct
proof safe
  fix m
  assume "t < m"
  assume "m \<le> t + dly"
  obtain x where "\<tau>2 m sig = None \<or> \<tau>2 m sig = Some x"
    by (meson not_None_eq)
  moreover
  { assume "\<tau>2 m sig = None"
    hence "check (\<tau>2 m) sig (\<sigma> sig)" by auto }
  moreover
  { assume "\<tau>2 m sig = Some x"
    hence "signal_of (\<sigma> sig) \<tau>2 sig m = x"
      by (meson option.inject trans_some_signal_of')
    hence "signal_of (\<sigma> sig) \<tau>1 sig m = x"
      using assms(2) by auto
    have *: "\<tau>1 m sig = None \<or> \<tau>1 m sig = Some x"
    proof (rule ccontr)
      assume "\<not> (\<tau>1 m sig = None \<or> \<tau>1 m sig = Some x)"
      hence "\<tau>1 m sig \<noteq> None \<and> \<tau>1 m sig \<noteq> Some x"
        by auto
      then obtain y where "y \<noteq> x" and "\<tau>1 m sig = Some y"
        using domD domIff by auto
      hence "signal_of (\<sigma> sig) \<tau>1 sig m = y"
        using trans_some_signal_of' by fastforce
      with `signal_of (\<sigma> sig) \<tau>1 sig m = x` and `y \<noteq> x` show False
        by auto
    qed
    moreover
    { assume "\<tau>1 m sig = Some x"
      hence "x = \<sigma> sig"
        using assms(1) unfolding is_stable_raw_correct using `t < m` `m \<le> t + dly`  by auto
      hence "check (\<tau>2 m) sig (\<sigma> sig)"
        using `\<tau>2 m sig = Some x` by auto }
    moreover
    { assume "\<tau>1 m sig = None"
      obtain k where "find (\<lambda>x. \<tau>1 x sig \<noteq> None) (rev [0..< m]) = None \<or>
                      find (\<lambda>x. \<tau>1 x sig \<noteq> None) (rev [0..< m]) = Some k"
        using option.exhaust_sel by blast
      moreover
      { assume "find (\<lambda>x. \<tau>1 x sig \<noteq> None) (rev [0..< m]) = None"
        hence "\<not> (\<exists>x. x \<in> set [0 ..< m] \<and> \<tau>1 x sig \<noteq> None)"
          unfolding find_None_iff by auto
        hence "\<And>x. x < m \<Longrightarrow> \<tau>1 x sig = None"
          by auto
        hence **: "\<And>x. x \<le> m \<Longrightarrow> \<tau>1 x sig = None"
          using `\<tau>1 m sig = None` using nat_less_le by blast
        have "signal_of (\<sigma> sig) \<tau>1 sig m = \<sigma> sig"
        proof -
          have "\<forall>t\<in>dom (to_trans_raw_sig \<tau>1 sig). m < t"
          proof (rule ccontr)
            assume "\<not>(\<forall>t\<in>dom (to_trans_raw_sig \<tau>1 sig). m < t)"
            then obtain t where "t \<in>dom (to_trans_raw_sig \<tau>1 sig)" and "t \<le> m"
              using leI by blast
            with ** have "\<tau>1 t sig = None"
              by auto
            hence "t \<notin> dom (to_trans_raw_sig \<tau>1 sig)"
              unfolding to_trans_raw_sig_def by auto
            thus False
              using \<open>t \<in> dom (to_trans_raw_sig \<tau>1 sig)\<close> by blast
          qed
          hence " Femto_VHDL_raw.inf_time (to_trans_raw_sig \<tau>1) sig m = None"
            by (auto simp add: inf_time_none_iff)
          thus ?thesis
            unfolding Femto_VHDL_raw.to_signal_def comp_def by auto
        qed
        hence "x = \<sigma> sig"
          using `signal_of (\<sigma> sig) \<tau>1 sig m = x` by auto
        hence "check (\<tau>2 m) sig (\<sigma> sig)"
          using `\<tau>2 m sig = Some x` by auto }
      moreover
      { assume "find (\<lambda>x. \<tau>1 x sig \<noteq> None) (rev [0..< m]) = Some k"
        hence " \<exists>i<length (rev [0..<m]). \<tau>1 (rev [0..<m] ! i) sig \<noteq> None
                                       \<and> k = rev [0..<m] ! i
                                       \<and> (\<forall>j<i. \<not> \<tau>1 (rev [0..<m] ! j) sig \<noteq> None)"
          unfolding find_Some_iff by auto
        then obtain i where "i<length (rev [0..<m])" and "\<tau>1 (rev [0..<m] ! i) sig \<noteq> None"
                      and "k = rev [0..<m] ! i " and quant: "\<forall>j<i.  \<tau>1 (rev [0..<m] ! j) sig = None"
          by auto
        have "k = m - i - 1" using `k = rev [0..<m] ! i`
          by (metis One_nat_def \<open>i < length (rev [0..<m])\<close> add.left_neutral add.right_neutral
              add_Suc_right diff_diff_add diff_less diff_zero length_rev length_upt nat_less_le
              neq0_conv nth_upt rev_nth zero_less_Suc zero_order(2))
        hence iless: "i < length ([0..<m])"
          using `i<length (rev [0..<m])` by auto
        have "\<tau>1 k sig \<noteq> None"
          using rev_nth[OF iless] `\<tau>1 (rev [0..<m] ! i) sig \<noteq> None` `k = m - i - 1`
          using \<open>k = rev [0..<m] ! i\<close> by auto
        have "\<And>j. j > k \<Longrightarrow>  j < m \<Longrightarrow> \<tau>1 j sig = None"
        proof -
          fix j
          assume "k < j" and "j < m"
          define j' where "j' = m - j - 1"
          have "m - i - 1 < j"
            using `k < j` unfolding `k  = m - i - 1` by auto
          hence "j' < i"
            unfolding j'_def  using `j < m` by linarith
          hence lookup: "\<tau>1 (rev [0..< m] ! j') sig = None"
            using quant by auto
          have "j' < m"
            unfolding j'_def using `j < m` by auto
          with rev_nth have "rev [0 ..< m] ! j' = [0 ..< m] ! j"
            unfolding j'_def  by (simp add: rev_nth Suc_diff_Suc \<open>j < m\<close> less_imp_le_nat)
          with lookup have "\<tau>1 ([0 ..< m] ! j) sig = None"
            by auto
          thus "\<tau>1 j sig = None"
            using nth_upt `j < m` by auto
        qed
        hence ind: "\<And>j. k < j \<Longrightarrow> j \<le> m \<Longrightarrow> \<tau>1 j sig = 0"
          using `\<tau>1 m sig = None` using dual_order.order_iff_strict  zero_option_def by fastforce
        have "t \<le> k"
        proof (rule ccontr)
          assume "\<not> (t \<le> k)" hence "k < t" by auto
          hence "\<tau>1 k sig = None"
            using assms(3)  by (simp add: zero_fun_def zero_option_def)
          with `\<tau>1 k sig \<noteq> None` show "False" by auto
        qed
        have "k < m"
          using \<open>i < length (rev [0..<m])\<close> \<open>k = m - i - 1\<close> by auto
        have "signal_of (\<sigma> sig) \<tau>1 sig m = signal_of (\<sigma> sig) \<tau>1 sig k"
          by (meson \<open>k < m\<close> ind less_imp_le_nat signal_of_less_ind')
        hence "signal_of (\<sigma> sig) \<tau>1 sig k = x"
          using `signal_of (\<sigma> sig) \<tau>1 sig m = x` by auto
        have "\<tau>1 k sig = None \<or> \<tau>1 k sig = Some x"
        proof (rule ccontr)
          assume "\<not> (\<tau>1 k sig = None \<or> \<tau>1 k sig = Some x)"
          hence "\<tau>1 k sig \<noteq> None \<and> \<tau>1 k sig \<noteq> Some x"
            by auto
          then obtain y where "y \<noteq> x" and "\<tau>1 k sig = Some y"
            using domD domIff by auto
          hence "signal_of (\<sigma> sig) \<tau>1 sig k = y"
            using trans_some_signal_of' by fastforce
          with `signal_of (\<sigma> sig) \<tau>1 sig k = x` and `y \<noteq> x` show False
            by auto
        qed
        with `\<tau>1 k sig \<noteq> None` have "\<tau>1 k sig = Some x"
          by auto
        have "t < k \<or> k = t"
          using `t \<le> k` by auto
        moreover
        { assume "t < k"
          hence "x = \<sigma> sig"
            using `\<tau>1 k sig = Some x` assms(1) unfolding is_stable_raw_correct
            using `t < k` `k < m` `m \<le> t + dly` by auto
          hence "check (\<tau>2 m) sig (\<sigma> sig)"
            using `\<tau>2 m sig = Some x` by auto }
        moreover
        { assume "t = k"
          hence "x = \<sigma> sig"
            using assms`\<tau>1 k sig = Some x`  by (simp add: zero_fun_def zero_option_def)
          hence "check (\<tau>2 m) sig (\<sigma> sig)"
            using `\<tau>2 m sig = Some x` by auto }
        ultimately have "check (\<tau>2 m) sig (\<sigma> sig)"
          by auto }
      ultimately have "check (\<tau>2 m) sig (\<sigma> sig)"
        by auto }
    ultimately have "check (\<tau>2 m) sig (\<sigma> sig)"
      by auto }
  ultimately show "check (\<tau>2 m) sig (\<sigma> sig)"
    by auto
qed

lemma signal_of_eq_is_stable_eq:
  assumes "\<And>n. n \<le> t \<Longrightarrow> \<tau>1 n = 0"
  assumes "\<And>n. n \<le> t \<Longrightarrow> \<tau>2 n = 0"
  assumes "\<And>k s. signal_of (\<sigma> s) \<tau>1 s k = signal_of (\<sigma> s) \<tau>2 s k"
  shows "is_stable_raw dly \<tau>1 t sig (\<sigma> sig) \<longleftrightarrow> is_stable_raw dly \<tau>2 t sig (\<sigma> sig)"
proof
  assume "is_stable_raw dly \<tau>1 t sig (\<sigma> sig)"
  with signal_of_eq_is_stable[OF _ assms(3) assms(1)] show "is_stable_raw dly \<tau>2 t sig (\<sigma> sig)"
    by auto
next
  assume "is_stable_raw dly \<tau>2 t sig (\<sigma> sig)"
  with signal_of_eq_is_stable[OF _ sym[OF assms(3)] assms(2)] show "is_stable_raw dly \<tau>1 t sig (\<sigma> sig)"
    by auto
qed

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

(* lemma signal_of_purged:
  assumes "k < t + dly"
  assumes "\<And>n. n \<le> t \<Longrightarrow> \<tau>1 n = 0"
  shows "signal_of (\<sigma> sig) (purge_raw \<tau>1 t dly sig) sig k = (\<sigma> sig)"
proof -
  have *: "\<And>k. k \<le> t \<Longrightarrow> (purge_raw \<tau>1 t dly sig) k = \<tau>1 k"
    using purge_raw_before_now_unchanged[of "\<tau>1" "t" "dly" "sig"] by auto
  have **: "\<And>k. k < t \<Longrightarrow> (purge_raw \<tau>1 t dly sig) k = 0"
    using assms(2) * by auto
  have "k < t \<or> k = t \<or> t < k"
    by auto
  moreover
  { assume "k < t "
    have ?thesis
    proof -
      have "\<forall>n\<in>dom ((to_trans_raw_sig (purge_raw \<tau>1 t dly sig) sig)). k < n"
      proof (rule ccontr)
        assume "\<not> (\<forall>n\<in>dom ((to_trans_raw_sig (purge_raw \<tau>1 t dly sig) sig)). k < n)"
        then obtain n where "n \<in> dom ((to_trans_raw_sig (purge_raw \<tau>1 t dly sig) sig))"
          and "n \<le> k"  using not_less by blast
        with `k < t` have "n < t" by auto
        hence "(purge_raw \<tau>1 t dly sig) n = \<tau>1 n "
          using * by auto
        also have "... = 0"
          using assms(2) `n < t` by auto
        finally have "(purge_raw \<tau>1 t dly sig) n = 0"
          by auto
        hence "n \<notin> dom ((to_trans_raw_sig (purge_raw \<tau>1 t dly sig) sig))"
          unfolding to_trans_raw_sig_def
          by (simp add: domIff zero_fun_def zero_option_def)
        with `n \<in> dom ((to_trans_raw_sig (purge_raw \<tau>1 t dly sig) sig))`
        show False by auto
      qed
      hence "Femto_VHDL_raw.inf_time (to_trans_raw_sig (purge_raw \<tau>1 t dly sig)) sig k = None"
        by (auto simp add: inf_time_none_iff)
      thus ?thesis
        unfolding Femto_VHDL_raw.to_signal_def comp_def by auto
    qed }
  moreover
  { assume "k = t"
    hence "(purge_raw \<tau>1 t dly sig) k sig = \<tau>1 k sig"
      using purge_raw_before_now_unchanged by (simp add: "*")
    obtain x where "\<tau>1 k sig = None \<or> \<tau>1 k sig = Some x"
      by (meson not_None_eq)
    moreover
    { assume "\<tau>1 k sig = None"
      have ?thesis
      proof -
        have "\<forall>n\<in>dom ((to_trans_raw_sig (purge_raw \<tau>1 t dly sig) sig)). k < n"
        proof (rule ccontr)
          assume "\<not> (\<forall>n\<in>dom ((to_trans_raw_sig (purge_raw \<tau>1 t dly sig) sig)). k < n)"
          then obtain n where "n \<in> dom ((to_trans_raw_sig (purge_raw \<tau>1 t dly sig) sig))"
            and "n \<le> k"  using not_less by blast
          with `k = t` have "n \<le> t" by auto
          hence "purge_raw \<tau>1 t dly sig n sig = \<tau>1 n sig"
            using * by auto
          also have "... = 0"
            using assms(2) `n \<le> t` `\<tau>1 k sig = None`
            by (metis \<open>k = t\<close> zero_fun_def zero_option_def)
          finally have "(purge_raw \<tau>1 t dly sig) n sig = 0"
            by auto
          hence "n \<notin> dom ((to_trans_raw_sig (purge_raw \<tau>1 t dly sig) sig))"
            unfolding to_trans_raw_sig_def by (simp add: domIff zero_fun_def zero_option_def)
          with `n \<in> dom ((to_trans_raw_sig (purge_raw \<tau>1 t dly sig) sig))`
          show False by auto
        qed
        hence "Femto_VHDL_raw.inf_time (to_trans_raw_sig (purge_raw \<tau>1 t dly sig)) sig k = None"
          by (auto simp add: inf_time_none_iff)
        thus ?thesis
          unfolding Femto_VHDL_raw.to_signal_def comp_def by auto
      qed }
    moreover
    { assume "\<tau>1 k sig = Some x"
      hence "x = \<sigma> sig"
        using assms by (simp add: \<open>k = t\<close> zero_fun_def zero_option_def)
      hence "\<tau>1 k sig = Some (\<sigma> sig)"
        using `\<tau>1 k sig = Some x` by auto
      hence ?thesis
        using \<open>(purge_raw \<tau>1 t dly sig) k sig = \<tau>1 k sig\<close> trans_some_signal_of'
        by fastforce }
    ultimately have ?thesis by auto }
  moreover
  { assume "t < k"
    have "(purge_raw \<tau>1 t dly sig) k sig = None \<or>
          (purge_raw \<tau>1 t dly sig) k sig = Some (\<sigma> sig)"
      by (simp add: \<open>t < k\<close> assms(1) order.strict_implies_order purge_raw_correctness')
    moreover
    { assume "(purge_raw \<tau>1 t dly sig) k sig = Some (\<sigma> sig)"
      hence ?thesis by (meson trans_some_signal_of') }
    moreover
    { assume "(purge_raw \<tau>1 t dly sig) k sig = None"
      define \<tau>1' where "\<tau>1' = purge_raw \<tau>1 t dly sig"
      obtain k' where "find (\<lambda>x. \<tau>1' x sig \<noteq> None) (rev [0..< k]) = None \<or>
                       find (\<lambda>x. \<tau>1' x sig \<noteq> None) (rev [0..< k]) = Some k'"
        using option.exhaust_sel by blast
      moreover
      { assume "find (\<lambda>x. \<tau>1' x sig \<noteq> None) (rev [0..< k]) = None"
        hence "\<not> (\<exists>x. x \<in> set [0 ..< k] \<and> \<tau>1' x sig \<noteq> None)"
          unfolding find_None_iff by auto
        hence "\<And>x. x < k \<Longrightarrow> \<tau>1' x sig = None"
          by auto
        hence ***: "\<And>x. x \<le> k \<Longrightarrow> \<tau>1' x sig = None"
          using `(purge_raw \<tau>1 t dly sig) k sig = None`
          unfolding \<tau>1'_def using nat_less_le by blast
        have "signal_of (\<sigma> sig) \<tau>1' sig k = \<sigma> sig"
        proof -
          have "\<forall>t\<in>dom ((to_trans_raw_sig \<tau>1' sig)). k < t"
          proof (rule ccontr)
            assume "\<not>(\<forall>t\<in>dom ((to_trans_raw_sig \<tau>1' sig)). k < t)"
            then obtain t where "t \<in>dom ((to_trans_raw_sig \<tau>1' sig))" and "t \<le> k"
              using leI by blast
            with *** have "\<tau>1' t sig = None"
              by auto
            hence "t \<notin> dom ((to_trans_raw_sig \<tau>1' sig))"
              unfolding to_trans_raw_sig_def by auto
            thus False
              using \<open>t \<in> dom ((to_trans_raw_sig \<tau>1' sig))\<close> by blast
          qed
          hence " Femto_VHDL_raw.inf_time (to_trans_raw_sig \<tau>1') sig k = None"
            by (auto simp add: inf_time_none_iff)
          thus ?thesis
            unfolding Femto_VHDL_raw.to_signal_def comp_def by auto
        qed
        hence ?thesis
          unfolding \<tau>1'_def by auto }
      moreover
      { assume "find (\<lambda>x. \<tau>1' x sig \<noteq> None) (rev [0..< k]) = Some k'"
        hence " \<exists>i<length (rev [0..<k]). \<tau>1' (rev [0..<k] ! i) sig \<noteq> None
                                       \<and> k' = rev [0..<k] ! i
                                       \<and> (\<forall>j<i. \<not> \<tau>1' (rev [0..<k] ! j) sig \<noteq> None)"
          unfolding find_Some_iff by auto
        then obtain i where "i<length (rev [0..<k])" and "\<tau>1' (rev [0..<k] ! i) sig \<noteq> None"
                      and "k' = rev [0..<k] ! i " and quant: "\<forall>j<i. \<tau>1' (rev [0..<k] ! j) sig = None"
          by auto
        have "k' = k - i - 1" using `k' = rev [0..<k] ! i`
          by (metis One_nat_def \<open>i < length (rev [0..<k])\<close> add.left_neutral add.right_neutral
              add_Suc_right diff_diff_add diff_less diff_zero length_rev length_upt nat_less_le
              neq0_conv nth_upt rev_nth zero_less_Suc zero_order(2))
        hence iless: "i < length ([0..<k])"
          using `i<length (rev [0..<k])` by auto
        have "\<tau>1' k' sig \<noteq> None"
          using rev_nth[OF iless] `\<tau>1' (rev [0..<k] ! i) sig \<noteq> None` `k' = k - i - 1`
          using \<open>k' = rev [0..<k] ! i\<close> by auto
        have "\<And>j. j > k' \<Longrightarrow>  j < k \<Longrightarrow> \<tau>1' j sig = None"
        proof -
          fix j
          assume "k'< j" and "j < k"
          define j' where "j' = k - j - 1"
          have "k - i - 1 < j"
            using `k'< j` unfolding `k' = k - i - 1` by auto
          hence "j' < i"
            unfolding j'_def  using `j < k` by linarith
          hence lookup: "\<tau>1' (rev [0..< k] ! j') sig = None"
            using quant by auto
          have "j' < k"
            unfolding j'_def using `j < k` by auto
          with rev_nth have "rev [0 ..< k] ! j' = [0 ..< k] ! j"
            unfolding j'_def  by (simp add: rev_nth Suc_diff_Suc \<open>j < k\<close> less_imp_le_nat)
          with lookup have "\<tau>1' ([0 ..< k] ! j) sig = None"
            by auto
          thus "\<tau>1' j sig = None"
            using nth_upt `j < k` by auto
        qed
        hence ind: "\<And>j. k' < j \<Longrightarrow> j \<le> k \<Longrightarrow> \<tau>1' j sig = 0"
          using `(purge_raw \<tau>1 t dly sig) k sig = None` unfolding \<tau>1'_def
          using dual_order.order_iff_strict  zero_option_def by fastforce
        have "k' < k"
          using \<open>i < length (rev [0..<k])\<close> \<open>k' = k - i - 1\<close> by auto
        hence " signal_of (\<sigma> sig) \<tau>1' sig k = signal_of (\<sigma> sig) \<tau>1' sig k'"
          by (metis \<open>\<tau>1' (rev [0..<k] ! i) sig \<noteq> None\<close> \<open>k' = rev [0..<k] ! i\<close> \<tau>1'_def assms(1)
          assms(2) leI less_imp_le_nat less_trans purge_raw_before_now_unchanged
          purge_raw_correctness' zero_fun_def zero_option_def)
        have "t \<le> k'"
        proof (rule ccontr)
          assume "\<not> t \<le> k'" hence "k' < t" by auto
          have "\<tau>1' k' sig = \<tau>1 k' sig"
            unfolding \<tau>1'_def  using "*" \<open>k' < t\<close> by auto
          also have "... = 0"
            using assms(2) `k' < t` by (simp add: zero_fun_def)
          finally have "\<tau>1' k' sig = 0"
            by auto
          with `\<tau>1' k' sig \<noteq> None` show False  by (simp add: zero_option_def)
        qed
        hence "t \<noteq> k' \<or> t = k'" by auto
        moreover
        { assume "t \<noteq> k'"
          hence "\<tau>1' k' sig = Some (\<sigma> sig)"
            unfolding \<tau>1'_def using `k' < k` `k < t + dly` `t \<le> k'` `\<tau>1' k' sig \<noteq> None`
            by (metis (no_types, lifting) \<tau>1'_def le_cases le_less_trans le_neq_trans less_irrefl purge_raw_correctness')
          hence "signal_of (\<sigma> sig) \<tau>1' sig k' = \<sigma> sig"
            by (meson trans_some_signal_of')
          with `signal_of (\<sigma> sig) \<tau>1' sig k = signal_of (\<sigma> sig) \<tau>1' sig k'`
          have ?thesis unfolding \<tau>1'_def by auto }
        moreover
        { assume "t = k'"
          have "\<tau>1' k' sig = \<tau>1 k' sig"
            using `t = k'` * unfolding \<tau>1'_def by auto
          obtain m where "\<tau>1 k' sig = None \<or> \<tau>1 k' sig = Some m"
            by (meson not_Some_eq)
          moreover
          { assume "\<tau>1 k' sig = Some m"
            hence "m = \<sigma> sig"
              using `t = k'` 
              by (simp add: assms(2) zero_fun_def zero_option_def)
            hence "\<tau>1 k' sig = Some (\<sigma> sig)"
              using `\<tau>1 k' sig = Some m` by auto
            hence "\<tau>1' k' sig = Some (\<sigma> sig)"
              using `\<tau>1' k' sig = \<tau>1 k' sig` by auto
            hence "signal_of (\<sigma> sig) \<tau>1' sig k' = \<sigma> sig"
              by (meson trans_some_signal_of')
            hence ?thesis
              using `signal_of (\<sigma> sig) \<tau>1' sig k = signal_of (\<sigma> sig) \<tau>1' sig k'`
              unfolding \<tau>1'_def by auto }
          moreover
          { assume "\<tau>1 k' sig = None"
            hence "\<tau>1' k' sig = None"
              using `\<tau>1' k' sig = \<tau>1 k' sig` by auto
            hence "signal_of (\<sigma> sig) \<tau>1' sig k = \<sigma> sig"
            proof -
              have "\<forall>n\<in>dom ((to_trans_raw_sig \<tau>1' sig)). k < n"
              proof (rule ccontr)
                assume "\<not> (\<forall>n\<in>dom ((to_trans_raw_sig \<tau>1' sig)). k < n)"
                then obtain n where "n \<in> dom ((to_trans_raw_sig \<tau>1' sig))" and "n \<le> k"
                  using \<open>\<tau>1' k' sig = None\<close> \<open>\<tau>1' k' sig \<noteq> None\<close> by blast
                have "\<tau>1' n sig = None"
                  using `n \<le> k` ** `\<tau>1' k' sig = None` `t = k'` unfolding \<tau>1'_def
                  using \<open>\<tau>1' k' sig \<noteq> None\<close> \<tau>1'_def by blast
                hence "n \<notin> dom ((to_trans_raw_sig \<tau>1' sig))"
                  by (transfer', auto simp add:to_trans_raw_sig_def)
                with `n \<in> dom ((to_trans_raw_sig \<tau>1' sig))` show False
                  by auto
              qed
              hence "Femto_VHDL_raw.inf_time (to_trans_raw_sig \<tau>1') sig k = None "
                by (auto simp add: inf_time_none_iff)
              thus ?thesis
                unfolding Femto_VHDL_raw.to_signal_def comp_def by auto
            qed
            hence ?thesis
              unfolding \<tau>1'_def by auto }
          ultimately have ?thesis by auto }
        ultimately have ?thesis by auto }
      ultimately have ?thesis by auto }
    ultimately have ?thesis by auto }
  ultimately show ?thesis by auto
qed *)

lemma helper':
  assumes "t, \<sigma>, \<gamma>, \<theta>1 \<turnstile> <ss, \<tau>1> \<longrightarrow>\<^sub>s \<tau>1'"
  assumes "\<And>k s. signal_of False \<theta>1 s k = signal_of False \<theta>2 s k"
  assumes "\<And>k s. signal_of (\<sigma> s) \<tau>1 s k = signal_of (\<sigma> s) \<tau>2 s k"
  assumes "t, \<sigma>, \<gamma>, \<theta>2 \<turnstile> <ss, \<tau>2> \<longrightarrow>\<^sub>s \<tau>2'"
  assumes "\<forall>n. n \<le> t \<longrightarrow>  \<tau>1 n = 0"
  assumes "\<forall>n. n \<le> t \<longrightarrow>  \<tau>2 n = 0"
  assumes "\<forall>n. t \<le> n \<longrightarrow>  \<theta>1 n = 0"
  assumes "\<forall>n. t \<le> n \<longrightarrow>  \<theta>2 n = 0"      
  assumes "nonneg_delay ss"
  assumes "\<forall>s. non_stuttering (to_trans_raw_sig \<tau>1) \<sigma> s"
  assumes "\<forall>s. non_stuttering (to_trans_raw_sig \<tau>2) \<sigma> s"
  shows "\<And>k s. signal_of (\<sigma> s) \<tau>1' s k = signal_of (\<sigma> s) \<tau>2' s k"
  using assms
proof (induction ss arbitrary:\<tau>1 \<tau>2 \<tau>1' \<tau>2')
  case (Bcomp ss1 ss2)
  then obtain \<tau> \<tau>' where tau1: "t , \<sigma> , \<gamma> , \<theta>1 \<turnstile> <ss1, \<tau>1> \<longrightarrow>\<^sub>s \<tau>" and tau2: "t , \<sigma> , \<gamma> , \<theta>1 \<turnstile> <ss2 , \<tau>> \<longrightarrow>\<^sub>s \<tau>1'"
      and tau3: "t , \<sigma> , \<gamma> , \<theta>2 \<turnstile> <ss1, \<tau>2> \<longrightarrow>\<^sub>s \<tau>'" and tau4: "t , \<sigma> , \<gamma> , \<theta>2 \<turnstile> <ss2 , \<tau>'> \<longrightarrow>\<^sub>s \<tau>2'"
      and "nonneg_delay ss1" and "nonneg_delay ss2"
    by auto
  have "\<And>k s. signal_of (\<sigma> s) \<tau> s k = signal_of (\<sigma> s) \<tau>' s k"
    using Bcomp(1)[OF tau1 Bcomp(4) Bcomp(5) tau3 Bcomp(7-10) `nonneg_delay ss1`] 
    using Bcomp.prems(10) Bcomp.prems(11) by blast
  moreover have "\<forall>n. n \<le> t \<longrightarrow>  \<tau> n = 0"
    using Bcomp(7) tau1 
    by (metis \<open>nonneg_delay ss1\<close> b_seq_exec_preserve_trans_removal dual_order.strict_implies_order
    nonneg_delay_same order.not_eq_order_implies_strict)
  moreover have "\<forall>n. n \<le> t \<longrightarrow> \<tau>' n = 0"
    using Bcomp(8) tau2
    by (metis \<open>nonneg_delay ss1\<close> b_seq_exec_preserve_trans_removal le_neq_implies_less le_refl
    nat_less_le nonneg_delay_same tau3)
  moreover  have "\<forall>a. non_stuttering (to_trans_raw_sig \<tau>) \<sigma> a"
    using b_seq_exec_preserves_non_stuttering Bcomp(12) tau1 
    by (metis Bcomp.prems(5) \<open>nonneg_delay ss1\<close>)
  moreover have "\<forall>a. non_stuttering (to_trans_raw_sig \<tau>') \<sigma> a"
    using b_seq_exec_preserves_non_stuttering Bcomp(13) tau2
    by (metis Bcomp.prems(6) \<open>nonneg_delay ss1\<close> tau3)
  ultimately show ?case
    using Bcomp(2)[OF tau2 Bcomp(4) _ tau4] `nonneg_delay ss2` Bcomp(9-10)  
    by blast
next
  case (Bguarded g ss1 ss2)
  hence "nonneg_delay ss1" and "nonneg_delay ss2"
    by auto
  have "beval_raw t \<sigma> \<gamma> \<theta>1 g \<or> \<not> beval_raw t \<sigma> \<gamma> \<theta>1 g"
    by auto
  moreover
  { assume "beval_raw t \<sigma> \<gamma> \<theta>1 g"
    hence "\<tau>1' = b_seq_exec t \<sigma> \<gamma> \<theta>1 ss1 \<tau>1"
      using Bguarded by auto
    have "beval_raw t \<sigma> \<gamma> \<theta>2 g"
      using beval_cong[OF Bguarded(4)] `beval_raw t \<sigma> \<gamma> \<theta>1 g` by auto
    hence "\<tau>2' = b_seq_exec t \<sigma> \<gamma> \<theta>2 ss1 \<tau>2"
      using Bguarded(6) by auto
    hence ?case
      using Bguarded(1) `\<tau>1' = b_seq_exec t \<sigma> \<gamma> \<theta>1 ss1 \<tau>1` Bguarded(4-5)
      Bguarded.prems(5) Bguarded.prems(6) \<open>nonneg_delay ss1\<close> assms(7) assms(8) 
      using Bguarded.prems(10) Bguarded.prems(11) by blast }
  moreover
  { assume "\<not> beval_raw t \<sigma> \<gamma> \<theta>1 g"
    hence "\<not> beval_raw t \<sigma> \<gamma> \<theta>2 g"
      using beval_cong[OF Bguarded(4)] by auto
    hence "\<tau>1' = b_seq_exec t \<sigma> \<gamma> \<theta>1 ss2 \<tau>1" and "\<tau>2' = b_seq_exec t \<sigma> \<gamma> \<theta>2 ss2 \<tau>2"
      using `\<not> beval_raw t \<sigma> \<gamma> \<theta>1 g` using Bguarded by auto
    hence ?case
      using Bguarded \<open>nonneg_delay ss2\<close> by blast }
  ultimately show ?case
    by auto
next
  case (Bassign_trans sig e dly)
  define x where "x = (beval_raw t \<sigma> \<gamma> \<theta>1 e)"
  hence "x = beval_raw t \<sigma> \<gamma> \<theta>2 e"
    using beval_cong[OF Bassign_trans(2)] by auto
  have tau1: "\<tau>1' = trans_post_raw sig x (\<sigma> sig) \<tau>1 t dly"
    using Bassign_trans(1)  using x_def by auto
  have tau2:  "\<tau>2' = trans_post_raw sig x (\<sigma> sig) \<tau>2 t dly"
    using Bassign_trans(4) using `x = beval_raw t \<sigma> \<gamma> \<theta>2 e`  by simp
  have "s \<noteq> sig \<Longrightarrow> signal_of (\<sigma> s) \<tau>1' s k = signal_of (\<sigma> s) \<tau>1 s k"
    using signal_of_trans_post unfolding tau1 by metis
  moreover have "s \<noteq> sig \<Longrightarrow> signal_of (\<sigma> s) \<tau>1 s k = signal_of (\<sigma> s) \<tau>2 s k"
    using Bassign_trans(3) by auto
  ultimately have *: "s \<noteq> sig \<Longrightarrow> signal_of (\<sigma> s) \<tau>1' s k = signal_of (\<sigma> s) \<tau>2' s k"
    using signal_of_trans_post unfolding tau2 by metis
  have "t + dly \<le> k \<or> k < t + dly"
    by auto
  moreover
  { assume "t + dly \<le> k"
    from signal_of_trans_post3[OF this] have "signal_of (\<sigma> sig) \<tau>1' sig k = x"
      by (metis Bassign_trans.prems(5) Bassign_trans.prems(9) dual_order.order_iff_strict  
      nonneg_delay.simps(4) tau1)
    moreover from signal_of_trans_post3[OF `t + dly \<le> k`] have "signal_of (\<sigma> sig) \<tau>2' sig k = x"
      by (metis Bassign_trans.prems(6) Bassign_trans.prems(9) less_imp_le_nat nonneg_delay.simps(4)
      tau2)
    ultimately have "signal_of (\<sigma> sig) \<tau>1' sig k = signal_of (\<sigma> sig) \<tau>2' sig k"
      by auto
    with * have "signal_of (\<sigma> s) \<tau>1' s k = signal_of (\<sigma> s) \<tau>2' s k"
      by auto }
  moreover
  { assume "k < t + dly"
    from signal_of_trans_post2[OF this] have "signal_of (\<sigma> s) \<tau>1' sig k = signal_of (\<sigma> s) \<tau>1 sig k"
      and "signal_of (\<sigma> s) \<tau>2' sig k = signal_of (\<sigma> s) \<tau>2 sig k" unfolding tau1 tau2 by metis+
    with * have "signal_of (\<sigma> s) \<tau>1' s k = signal_of (\<sigma> s) \<tau>2' s k"
      using Bassign_trans(3) by auto }
  ultimately show ?case by auto
next
  case (Bassign_inert sig e dly)
  define x where "x = (beval_raw t \<sigma> \<gamma> \<theta>1 e)"
  hence "x = beval_raw t \<sigma> \<gamma> \<theta>2 e"
    using beval_cong[OF Bassign_inert(2)] by auto
  have tau1: "\<tau>1' = inr_post_raw sig x (\<sigma> sig) \<tau>1 t dly"
    using Bassign_inert(1)  using x_def by auto
  have tau2:  "\<tau>2' = inr_post_raw sig x (\<sigma> sig) \<tau>2 t dly"
    using Bassign_inert(4) using `x = beval_raw t \<sigma> \<gamma> \<theta>2 e`  by simp
  have "s \<noteq> sig \<or> s = sig"
    by auto
  moreover
  { assume "s \<noteq> sig"
    hence ?case
      using inr_post_raw_does_not_affect_other_sig Bassign_inert(3) 
      unfolding tau1 tau2 
      by (metis (no_types, lifting) inr_post_raw_def signal_of_purge_not_affected
      signal_of_trans_post) }
  moreover
  { assume "s = sig"
    have "signal_of (\<sigma> s) \<tau>1 s t \<noteq> x \<and> signal_of (\<sigma> s) \<tau>1 s (t + dly) \<noteq> (\<not> x) 
        \<or> (signal_of (\<sigma> s) \<tau>1 s t = x \<or> signal_of (\<sigma> s) \<tau>1 s (t + dly) = (\<not> x))" (is "?earlier \<or> ?later")
      by auto
    moreover
    { assume "?earlier"
      hence earlier': "signal_of (\<sigma> s) \<tau>2 s t \<noteq> x" and "signal_of (\<sigma> s) \<tau>2  s (t + dly) \<noteq> (\<not> x)"
        using Bassign_inert(3) by auto
      hence "\<exists>n>t. n \<le> t + dly \<and> \<tau>2 n s = Some x"
        using switch_signal_ex_mapping[of "\<sigma>", OF earlier'] 
        by (simp add: Bassign_inert.prems(6) zero_fun_def)
      have "\<exists>n > t. n \<le> t + dly \<and> \<tau>1 n s = Some x"
        using switch_signal_ex_mapping[of "\<sigma>"] `?earlier`
        by (simp add: Bassign_inert.prems(5) zero_fun_def)
      let ?time = "GREATEST n. n \<le> t + dly \<and> \<tau>1 n s = Some x"
      let ?time2 = "GREATEST n. n \<le> t + dly \<and> \<tau>2 n s = Some x"
      have "?time \<le> ?time2"
      proof (rule Greatest_le_nat[where b="t + dly"])
        have "?time \<le> t + dly" and "\<tau>1 ?time s = Some x"
          using GreatestI_ex_nat[where P="\<lambda>n. n \<le> t + dly \<and> \<tau>1 n s = Some x" and b="t + dly"]
          `\<exists>n > t. n \<le> t + dly \<and> \<tau>1 n s = Some x` by blast+
        hence "0 < ?time"
          using Bassign_inert(5) 
          by (metis (full_types) not_gr_zero option.simps(3) zero_fun_def zero_le zero_option_def)
        have "\<tau>2 ?time s = Some x"
        proof (rule ccontr)
          assume "\<not> \<tau>2 ?time s = Some x"
          hence "\<tau>2 ?time s = None \<or> \<tau>2 ?time s = Some (\<not> x)"
            using option.inject by fastforce
          moreover
          { assume "\<tau>2 ?time s = Some (\<not> x)"
            hence "signal_of (\<sigma> s) \<tau>2 s ?time = (\<not> x)"
              using trans_some_signal_of' by fastforce
            moreover have "signal_of (\<sigma> s) \<tau>1 s ?time = x"
              using `\<tau>1 ?time s = Some x`  trans_some_signal_of' by fastforce
            ultimately have "False"
              using Bassign_inert(3) by blast }
          moreover
          { assume "\<tau>2 ?time s = None"
            hence "signal_of (\<sigma> s) \<tau>2 s ?time = signal_of (\<sigma> s) \<tau>2 s (?time - 1)"
              by (metis (no_types, lifting) signal_of_less_sig zero_option_def)
            also have "... = signal_of (\<sigma> s) \<tau>1 s (?time - 1)"
              using Bassign_inert(3) by blast
            also have "... \<noteq> signal_of (\<sigma> s) \<tau>1 s ?time"
            proof (rule ccontr)
              assume "\<not> signal_of (\<sigma> s) \<tau>1 s (?time - 1) \<noteq> signal_of (\<sigma> s) \<tau>1 s ?time"
              hence th: "signal_of (\<sigma> s) \<tau>1 s ?time = signal_of (\<sigma> s) \<tau>1 s (?time - 1)"
                by auto
              have "non_stuttering (to_trans_raw_sig \<tau>1) \<sigma> s"
                using Bassign_inert(10) by auto
              hence "\<tau>1 ?time s = 0"
                using current_sig_and_prev_same[where state="\<sigma>", OF th `0 < ?time`] by auto
              with `\<tau>1 ?time s = Some x` show False
                by (simp add: zero_option_def) 
            qed
            finally have "signal_of (\<sigma> s) \<tau>2 s ?time \<noteq> signal_of (\<sigma> s) \<tau>1 s ?time"
              by auto
            with Bassign_inert(3) have False
              by blast }
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
          hence "\<tau>1 ?time2 s = None \<or> \<tau>1 ?time2 s = Some (\<not> x)"
            using option.inject by fastforce
          moreover
          { assume "\<tau>1 ?time2 s = Some (\<not> x)"
            hence "signal_of (\<sigma> s) \<tau>1 s ?time2 = (\<not> x)"
              by (meson Bassign_inert.prems(5) \<open>signal_of (\<sigma> s) \<tau>1 s t \<noteq> x \<and> post_necessary_raw dly
              \<tau>1 t s (\<not> x) (\<sigma> s)\<close> trans_some_signal_of')
            with `signal_of (\<sigma> s) \<tau>2 s ?time2 = x` have False
              using Bassign_inert(3) by blast }
          moreover
          { assume "\<tau>1 ?time2 s = None"
            hence "signal_of (\<sigma> s) \<tau>1 s ?time2 = signal_of (\<sigma> s) \<tau>1 s (?time2 - 1)"
              by (metis (no_types, lifting) signal_of_less_sig zero_option_def)
            also have "... = signal_of (\<sigma> s) \<tau>2 s (?time2 - 1)"
              using Bassign_inert(3) by blast
            also have "... \<noteq> signal_of (\<sigma> s) \<tau>2 s ?time2"
              using current_sig_and_prev_same 
              by (metis (no_types, lifting) Bassign_inert.prems(11) Bassign_inert.prems(6) \<open>\<tau>2
              (GREATEST n. n \<le> t + dly \<and> \<tau>2 n s = Some x) s = Some x\<close> not_gr_zero option.simps(3)
              zero_fun_def zero_le zero_option_def)
            finally have "False"
              using Bassign_inert(3)  by blast }
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
          using signal_of_inr_post_before_now[OF `k < t`] Bassign_inert(5)
          by (metis Bassign_inert.prems(6) \<open>s = sig\<close> less_imp_le_nat) }
      moreover
      { assume "t \<le> k \<and> k < ?time"
        moreover have "\<sigma> s = (\<not> x)"
          using `?earlier` Bassign_inert(5) 
          by (metis signal_of_less_ind' signal_of_zero zero_fun_def zero_le)
        moreover have "signal_of (\<sigma> s) \<tau>1 s (t + dly) = x" and  "signal_of (\<sigma> s) \<tau>2 s (t + dly) = x"
          using `?earlier` earlier' \<open>post_necessary_raw dly \<tau>2 t s (\<not> x) (\<sigma> s)\<close> by blast+
        ultimately have "signal_of (\<sigma> s) (inr_post_raw s x (\<sigma> s) \<tau>1 t dly) s k = \<sigma> s"
          unfolding tau1  using Bassign_inert(5) 
          by (intro signal_of_inr_post2) auto
        moreover have "signal_of (\<sigma> s) (inr_post_raw s x (\<sigma> s) \<tau>2 t dly) s k = \<sigma> s"
          unfolding tau2 using `t \<le> k \<and> k < ?time` Bassign_inert(6) `\<sigma> s = (\<not> x)` `signal_of (\<sigma> s)
          \<tau>2 s (t + dly) = x` `t \<le> k \<and> k < ?time` `?time \<le> ?time2`
          by (intro signal_of_inr_post2) auto
        ultimately have ?case
          unfolding tau1 tau2  by (simp add: \<open>s = sig\<close>) }
      moreover
      { assume "?time \<le> k \<and> k < t + dly"
        have "signal_of (\<sigma> s) \<tau>1 s t \<noteq> x"
          using `?earlier` by auto
        moreover have "signal_of (\<sigma> s) \<tau>1 s (t + dly) \<noteq> (\<not> x)"
          using `?earlier` by auto
        moreover have "?time \<le> k"
          using `?time \<le> k \<and> k < t + dly` by auto
        moreover have "\<And>n. n \<le> t \<Longrightarrow> \<tau>1 n = 0"
          by (simp add: Bassign_inert.prems(5))
        ultimately have "signal_of (\<sigma> s) (inr_post_raw sig x (\<sigma> sig) \<tau>1 t dly) s k = x"
          unfolding `s = sig` by (intro signal_of_inr_post4)
        have "signal_of (\<sigma> s) \<tau>2 s t \<noteq> x"
          using earlier' by auto
        moreover have "signal_of (\<sigma> s) \<tau>2 s (t + dly) \<noteq> (\<not> x)"
          using \<open>post_necessary_raw dly \<tau>2 t s (\<not> x) (\<sigma> s)\<close> by blast
        moreover have "?time2 \<le> k"
          using `?time \<le> k \<and> k < t + dly` `?time2 \<le> ?time` by auto
        moreover have "\<And>n. n \<le> t \<Longrightarrow> \<tau>2 n = 0"
          by (simp add: Bassign_inert.prems(6))
        ultimately have "signal_of (\<sigma> s) (inr_post_raw sig x (\<sigma> sig) \<tau>2 t dly) s k = x"
          unfolding `s = sig` by (intro signal_of_inr_post4) 
        hence ?case
          using \<open>signal_of (\<sigma> s) (inr_post_raw sig x (\<sigma> sig) \<tau>1 t dly) s k = x\<close> tau1 tau2 by blast }
      moreover
      { assume "t + dly \<le> k"
        hence ?case
          by (smt Bassign_inert.prems(5) Bassign_inert.prems(6) Suc_leI \<open>\<exists>n>t. n \<le> t + dly \<and> \<tau>2 n s
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
          unfolding tau1 tau2 using signal_of_inr_post_before_now[OF `k < t`] Bassign_inert(5)
          by (metis Bassign_inert.prems(6) \<open>s = sig\<close> less_imp_le_nat) }
      moreover
      { assume "t \<le> k \<and> k < t + dly"
        hence "t \<le> k" and "k < t + dly"
          by auto
        have "signal_of (\<sigma> s) \<tau>1' s k = \<sigma> s"
          unfolding tau1 using signal_of_inr_post3[OF `t \<le> k` `k < t + dly`] `?later` `s = sig` 
          by (metis (mono_tags, lifting) Bassign_inert.prems(5))
        also have "... = signal_of (\<sigma> s) \<tau>2' s k"
          unfolding tau2 using signal_of_inr_post3[OF `t \<le> k` `k < t + dly`] `?later` `s = sig` 
          by (metis (mono_tags, lifting) Bassign_inert.prems(3) Bassign_inert.prems(6))
        finally have ?case
          by auto }
      moreover
      { assume "t + dly \<le> k"
        have ?case
          unfolding tau1 tau2 using signal_of_inr_post[OF `t + dly \<le> k`] `s = sig` 
          by (metis Bassign_inert.prems(5) Bassign_inert.prems(6) Bassign_inert.prems(9) less_imp_le_nat nonneg_delay.simps(5)) }
      ultimately have ?case
        by auto }
    ultimately have ?case 
      by auto }
  ultimately show ?case
    by auto 
next
  case Bnull
  then show ?case by auto
qed

lemma helper:
  assumes "t, \<sigma>, \<gamma>, \<theta>1 \<turnstile> <ss, \<tau>1> \<longrightarrow>\<^sub>s \<tau>1'"
  assumes "\<And>k s. signal_of False \<theta>1 s k = signal_of False \<theta>2 s k"
  assumes "\<And>k s. signal_of (\<sigma> s) \<tau>1 s k = signal_of (\<sigma> s) \<tau>2 s k"
  assumes "\<forall>n. n \<le> t \<longrightarrow>  \<tau>1 n = 0"
  assumes "\<forall>n. n \<le> t \<longrightarrow>  \<tau>2 n = 0"
  assumes "\<forall>n. t \<le> n \<longrightarrow>  \<theta>1 n = 0"
  assumes "\<forall>n. t \<le> n \<longrightarrow>  \<theta>2 n = 0"        
  assumes "nonneg_delay ss"
  assumes "\<forall>s. non_stuttering (to_trans_raw_sig \<tau>1) \<sigma> s"
  assumes "\<forall>s. non_stuttering (to_trans_raw_sig \<tau>2) \<sigma> s"
  shows "\<exists>\<tau>2'. (t, \<sigma>, \<gamma>, \<theta>2 \<turnstile> <ss, \<tau>2> \<longrightarrow>\<^sub>s \<tau>2') \<and> (\<forall>k s. signal_of (\<sigma> s) \<tau>1' s k = signal_of (\<sigma> s) \<tau>2' s k)"
  using helper'[OF assms(1-3) _ assms(4-10)] `nonneg_delay ss`  by blast

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
  "\<forall>s. non_stuttering (to_trans_raw_sig (derivative_raw w t)) (\<lambda>s. w s t) s"
proof 
  fix s
  define ks where "ks = keys (to_trans_raw_sig (derivative_raw w t) s)"
  { fix k1 k2 :: nat 
    assume "k1 < k2" and "k1 \<in> ks" and "k2 \<in> ks"
    assume "\<forall>k. k1 < k \<and> k < k2 \<longrightarrow> k \<notin> ks"
    have "t < k1"
      using `k1 \<in> ks` unfolding ks_def by (simp add: keys_at_least_t)
    hence "to_trans_raw_sig (derivative_raw w t) s k1 = Some (w s k1)"
      using `k1 \<in> ks` unfolding ks_def keys_def to_trans_raw_sig_def derivative_raw_def
      difference_raw_def  using CollectD zero_option_def by fastforce
    moreover have "to_trans_raw_sig (derivative_raw w t) s k2 = Some (w s k2)"
      using `k2 \<in> ks` CollectD zero_option_def `t < k1` `k1 < k2`
      unfolding ks_def keys_def to_trans_raw_sig_def derivative_raw_def difference_raw_def
      by fastforce
    moreover have "w s k1 \<noteq> w s k2"
    proof -
      have "\<forall>k. k1 < k \<and> k < k2 \<longrightarrow> w s k = w s k1"
      proof (rule, rule)
        fix k
        assume "k1 < k \<and> k < k2"
        hence "signal_of (w s t) (derivative_raw w t) s k = w s k"
          using `t < k1`
          by(intro signal_of_derivative_raw[where \<sigma>="\<lambda>s. w s t"])(auto)
        hence "w s k = signal_of (w s t) (derivative_raw w t) s k"          
          by auto
        also have "... = signal_of (w s t) (derivative_raw w t) s k1"
          using `\<forall>k. k1 < k \<and> k < k2 \<longrightarrow> k \<notin> ks` `k1 < k \<and> k < k2` unfolding ks_def
          by (intro signal_of_less_ind')(simp add: keys_def to_trans_raw_sig_def)+
        also have "... = w s k1"
          using `t < k1`
          by(intro signal_of_derivative_raw[where \<sigma>="\<lambda>s. w s t"])(auto)
        finally show "w s k = w s k1"
          by auto
      qed
      hence "w s (k2 - 1) = w s k1"
        using `k1 < k2` `t < k1` 
        by (metis Suc_diff_1 diff_less less_SucE less_Suc_eq_0_disj less_imp_Suc_add zero_less_one)
      moreover have "w s k2 \<noteq> w s (k2 - 1)"
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
    hence "\<And>k. t \<le> k \<and> k < Least_key \<Longrightarrow> w s k = w s t"
    proof -
      fix k
      assume "t \<le> k \<and> k < Least_key"
      hence "signal_of (w s t) (derivative_raw w t) s k = w s k"
        by (intro signal_of_derivative_raw)(auto)
      hence "w s k = signal_of (w s t) (derivative_raw w t) s k "
        by auto
      also have "... = signal_of (w s t) (derivative_raw w t) s t"
        using `t \<le> k \<and> k < Least_key` `\<And>k. k < Least_key \<Longrightarrow> k \<notin> ks` `t \<le> k \<and> k < Least_key` 
        by (intro signal_of_less_ind')(simp add: keys_def ks_def to_trans_raw_sig_def)+
      also have "... = signal_of (w s t) (derivative_raw w t) s 0"
        by (intro signal_of_less_ind')(auto simp add: derivative_raw_def zero_option_def)
      also have "... = w s t"
        by (metis (full_types) derivative_raw_def signal_of_zero zero_option_def zero_order(1))
      finally show "w s k = w s t"
        by auto 
    qed
    moreover have "w s Least_key \<noteq> w s (Least_key - 1)"
      using `Least_key \<in> ks` `t < Least_key` unfolding ks_def keys_def to_trans_raw_sig_def
      derivative_raw_def difference_raw_def  using zero_option_def by force
    ultimately have "w s t \<noteq> w s Least_key"
      by (metis Suc_diff_1 \<open>t < Least_key\<close> diff_less less_Suc_eq_0_disj less_Suc_eq_le
      less_imp_Suc_add zero_less_one)
    moreover have "Some (w s Least_key) = to_trans_raw_sig (derivative_raw w t) s Least_key"
      using `Least_key \<in> ks` `t < Least_key` unfolding ks_def keys_def to_trans_raw_sig_def
      derivative_raw_def difference_raw_def using \<open>w s Least_key \<noteq> w s (Least_key - 1)\<close> by auto
    ultimately have "w s t \<noteq> the (to_trans_raw_sig (derivative_raw w t) s (LEAST k. k \<in> ks))"
      unfolding Least_key_def by (metis option.sel) }
  with first_po show "non_stuttering (to_trans_raw_sig (derivative_raw w t)) (\<lambda>s. w s t) s"
    unfolding non_stuttering_def ks_def  by blast
qed

lemma destruct_worldline_ensure_non_stuttering:
  assumes "destruct_worldline tw = (t, \<sigma>, \<gamma>, \<theta>, \<tau>)"
  shows "\<forall>s. non_stuttering (to_trans_raw_sig \<tau>) \<sigma> s"
proof -
  have "\<tau> = derivative_raw (snd tw) t"     
    using assms  by (metis (no_types, lifting) Pair_inject destruct_worldline_def)
  moreover have  "\<sigma> = (\<lambda>s. snd tw s t)"
  proof -
    { fix aa :: 'a
      have "(get_time tw, \<lambda>a. snd tw a (get_time tw), {a. snd tw a (get_time tw) = (\<not> signal_of False (derivative_hist_raw (snd tw) (get_time tw)) a (get_time tw - 1))}, derivative_hist_raw (snd tw) (get_time tw), derivative_raw (snd tw) (get_time tw)) = (t, \<sigma>, \<gamma>, \<theta>, \<tau>)"
        by (metis assms destruct_worldline_def)
      then have "\<not> \<sigma> aa \<and> \<not> snd tw aa t \<or> \<sigma> aa \<and> snd tw aa t"
        by blast }
    then show "\<sigma> = (\<lambda>a. snd tw a t)"
      by blast
  qed
  ultimately show "\<forall>s. non_stuttering (to_trans_raw_sig \<tau>) \<sigma> s"
    using derivative_raw_ensure_non_stuttering[of "snd tw" "t"] by auto
qed

lemma Bcomp_hoare_valid':
  assumes "\<Turnstile> [P] s1 [Q]" and "\<Turnstile> [Q] s2 [R]"
  assumes "nonneg_delay (Bcomp s1 s2)"
  shows "\<Turnstile> [P] Bcomp s1 s2 [R]"
  unfolding seq_hoare_valid2_def
proof (rule)+
  fix tw tw' :: "nat \<times> 'a worldline"
  have "nonneg_delay s1" and "nonneg_delay s2"
    using assms(3) by auto
  assume "P tw \<and> (tw, Bcomp s1 s2 \<Rightarrow>\<^sub>s tw')"
  hence "P tw" and "tw, Bcomp s1 s2 \<Rightarrow>\<^sub>s tw'" by auto
  then obtain t \<sigma> \<gamma> \<theta> \<tau> \<tau>' where des: "destruct_worldline tw = (t, \<sigma>, \<gamma>, \<theta>, \<tau>)" and
    "(t, \<sigma>, \<gamma>, \<theta> \<turnstile> <Bcomp s1 s2, \<tau>> \<longrightarrow>\<^sub>s \<tau>')" and "tw'= worldline2 t \<sigma> \<theta> \<tau>'"
    unfolding world_seq_exec_def Let_def using destruct_worldline_exist by fastforce
  have "\<forall>s. non_stuttering (to_trans_raw_sig \<tau>) \<sigma> s"
    using destruct_worldline_ensure_non_stuttering[OF des] by auto
  hence "\<forall>s. non_stuttering (to_trans_raw_sig \<tau>') \<sigma> s"
    using b_seq_exec_preserves_non_stuttering[OF _ `t, \<sigma>, \<gamma>, \<theta> \<turnstile> <Bcomp s1 s2, \<tau>> \<longrightarrow>\<^sub>s \<tau>'`]
    by (meson assms(3) context_invariant_def des worldline2_constructible)
  then obtain \<tau>'' where tau1: "(t, \<sigma>, \<gamma>, \<theta> \<turnstile> <s1, \<tau>> \<longrightarrow>\<^sub>s \<tau>'')" and tau2: "(t, \<sigma>, \<gamma>, \<theta> \<turnstile> <s2, \<tau>''> \<longrightarrow>\<^sub>s \<tau>')"
    using \<open>t , \<sigma> , \<gamma> , \<theta> \<turnstile> <Bcomp s1 s2 , \<tau>> \<longrightarrow>\<^sub>s \<tau>'\<close> by auto
  have "\<forall>s. non_stuttering (to_trans_raw_sig \<tau>'') \<sigma> s"
    using b_seq_exec_preserves_non_stuttering[OF _ tau1]
    by (meson \<open>\<forall>s. non_stuttering (to_trans_raw_sig \<tau>) \<sigma> s\<close> assms(3) context_invariant_def des
    nonneg_delay.simps(2) worldline2_constructible)
  define tw'' where "tw'' = worldline2 t \<sigma> \<theta> \<tau>''"
  hence "tw, s1 \<Rightarrow>\<^sub>s tw''"
    using des tau1 unfolding world_seq_exec_def Let_def by auto
  with assms(1) have "Q tw''"
    unfolding seq_hoare_valid2_def using `P tw` by fastforce
  have "context_invariant t \<sigma> \<gamma> \<theta> \<tau>"
    using worldline2_constructible[OF des] by auto
  hence "context_invariant t \<sigma> \<gamma> \<theta> \<tau>''"
    using b_seq_exec_preserves_context_invariant[OF _ tau1] assms(3) by auto
  obtain \<theta>''' \<tau>''' where des2: "destruct_worldline tw'' = (t, \<sigma>, \<gamma>, \<theta>''', \<tau>''')" and
    sig_beh: "\<And>k s. signal_of False \<theta> s k = signal_of False \<theta>''' s k" and
    sig_trans: "\<And>k s. signal_of (\<sigma> s) \<tau>'' s k = signal_of (\<sigma> s) \<tau>''' s k"
    unfolding tw''_def using destruct_worldline_correctness[OF `context_invariant t \<sigma> \<gamma> \<theta> \<tau>''`]
    by (metis destruct_worldline_exist)
  have "\<forall>s. non_stuttering (to_trans_raw_sig \<tau>''') \<sigma> s"
    using destruct_worldline_ensure_non_stuttering[OF des2] by blast
  have "context_invariant t \<sigma> \<gamma> \<theta>''' \<tau>'''"
    using worldline2_constructible[OF des2] by auto
  obtain \<tau>4 where tau3: "t, \<sigma>, \<gamma>, \<theta>''' \<turnstile> <s2, \<tau>'''> \<longrightarrow>\<^sub>s \<tau>4" and
    sig_trans: "\<And>k s. signal_of (\<sigma> s) \<tau>4 s k = signal_of (\<sigma> s) \<tau>' s k"
    using helper[OF tau2 sig_beh sig_trans ]  \<open>nonneg_delay s2\<close> `context_invariant t \<sigma> \<gamma> \<theta> \<tau>''`
    `context_invariant t \<sigma> \<gamma> \<theta>''' \<tau>'''` `\<forall>s. non_stuttering (to_trans_raw_sig \<tau>'') \<sigma> s`
    `\<forall>s. non_stuttering (to_trans_raw_sig \<tau>''') \<sigma> s` unfolding context_invariant_def
    by simp
  have "worldline2 t \<sigma> \<theta> \<tau>' = worldline2 t \<sigma> \<theta>''' \<tau>4"
    unfolding worldline2_def worldline_raw_def  using sig_beh sig_trans by auto
  hence "tw'', s2 \<Rightarrow>\<^sub>s tw'"
    unfolding world_seq_exec_def using des2 tau3 `tw'= worldline2 t \<sigma> \<theta> \<tau>'`
    by (smt \<open>t, \<sigma> , \<gamma> , \<theta> \<turnstile> <Bcomp s1 s2 , \<tau>> \<longrightarrow>\<^sub>s \<tau>'\<close> \<open>tw , Bcomp s1 s2 \<Rightarrow>\<^sub>s tw'\<close> case_prod_conv
    des fst_conv world_seq_exec_def)
  with `Q tw''` show "R tw'"
    using assms(2) unfolding seq_hoare_valid2_def by blast
qed

lemma Bnull_sound_hoare2:
  "\<turnstile> [P] Bnull [Q] \<Longrightarrow> \<Turnstile> [P] Bnull [Q]"
  by (auto dest!: BnullE'_hoare2 worldline2_constructible  simp add: seq_hoare_valid2_def world_seq_exec_def
           split: prod.splits)

lemma Bguarded_hoare_valid2:
  assumes "\<Turnstile> [\<lambda>tw. P tw \<and> beval_world_raw2 tw g] s1 [Q]" and "\<Turnstile> [\<lambda>tw. P tw \<and> \<not> beval_world_raw2 tw g] s2 [Q]"
  shows "\<Turnstile> [P] Bguarded g s1 s2 [Q]"
  unfolding seq_hoare_valid2_def
proof (rule)+
  fix tw  tw':: "nat \<times> 'a worldline"
  assume "P tw \<and> (tw, Bguarded g s1 s2 \<Rightarrow>\<^sub>s tw')"
  hence "P tw" and "tw, Bguarded g s1 s2 \<Rightarrow>\<^sub>s tw'" by auto
  obtain t \<sigma> \<gamma> \<theta> \<tau> where "destruct_worldline tw = (t, \<sigma>, \<gamma>, \<theta>, \<tau>)"
    by (meson destruct_worldline_def)
  hence "fst tw = t" and "tw = worldline2 t \<sigma> \<theta> \<tau> " and "context_invariant t \<sigma> \<gamma> \<theta> \<tau>"
    by(auto dest!: worldline2_constructible)
  obtain \<tau>' where "t , \<sigma> , \<gamma> , \<theta> \<turnstile> <Bguarded g s1 s2, \<tau>> \<longrightarrow>\<^sub>s \<tau>'"
    by auto
  hence "tw' = worldline2 t \<sigma> \<theta> \<tau>'"
    using `tw, Bguarded g s1 s2 \<Rightarrow>\<^sub>s tw'` `destruct_worldline tw = (t, \<sigma>, \<gamma>, \<theta>, \<tau>)`
    unfolding world_seq_exec_def by auto
  have "beval_raw t \<sigma> \<gamma> \<theta> g \<or> \<not> beval_raw t \<sigma> \<gamma> \<theta> g"
    by auto
  moreover
  { assume "beval_raw t \<sigma> \<gamma> \<theta> g"
    hence "t, \<sigma>, \<gamma>, \<theta> \<turnstile> <s1, \<tau>> \<longrightarrow>\<^sub>s \<tau>'"
      using `t, \<sigma>, \<gamma>, \<theta> \<turnstile> <Bguarded g s1 s2, \<tau>> \<longrightarrow>\<^sub>s \<tau>'` by auto
    hence "beval_world_raw2 tw g"
      using `beval_raw t \<sigma> \<gamma> \<theta> g` `tw = worldline2 t \<sigma> \<theta> \<tau>` `context_invariant t \<sigma> \<gamma> \<theta> \<tau>`
      by (metis \<open>fst tw = t\<close> beval_beval_world_raw_ci beval_world_raw2_def snd_conv worldline2_def)
    have "tw , s1 \<Rightarrow>\<^sub>s tw'"
      using `destruct_worldline tw = (t, \<sigma>, \<gamma>, \<theta>, \<tau>)` `t, \<sigma>, \<gamma>, \<theta> \<turnstile> <s1, \<tau>> \<longrightarrow>\<^sub>s \<tau>'`
      `tw' = worldline2 t \<sigma> \<theta> \<tau>'` unfolding world_seq_exec_def Let_def  by simp
    with assms(1) and `P tw` have "Q tw'"
      using `beval_world_raw2 tw g` `fst tw = t` unfolding seq_hoare_valid2_def by blast }
  moreover
  { assume "\<not> beval_raw t \<sigma> \<gamma> \<theta> g"
    hence "t, \<sigma>, \<gamma>, \<theta> \<turnstile> <s2, \<tau>> \<longrightarrow>\<^sub>s \<tau>'"
      using `t, \<sigma>, \<gamma>, \<theta> \<turnstile> <Bguarded g s1 s2, \<tau>> \<longrightarrow>\<^sub>s \<tau>'` by auto
    hence "\<not> beval_world_raw2 tw g"
      using `\<not> beval_raw t \<sigma> \<gamma> \<theta> g` `tw = worldline2 t \<sigma> \<theta> \<tau>` `context_invariant t \<sigma> \<gamma> \<theta> \<tau>`
      by (metis \<open>fst tw = t\<close> beval_beval_world_raw_ci beval_world_raw2_def snd_conv worldline2_def)
    have "tw, s2 \<Rightarrow>\<^sub>s tw'"
      using `destruct_worldline tw = (t, \<sigma>, \<gamma>, \<theta>, \<tau>)` `t, \<sigma>, \<gamma>, \<theta> \<turnstile> <s2, \<tau>> \<longrightarrow>\<^sub>s \<tau>'`
      `tw' = worldline2 t \<sigma> \<theta> \<tau>'` unfolding world_seq_exec_def Let_def
      by simp
    with assms(2) and `P tw` have "Q tw'"
      using `\<not> beval_world_raw2 tw g` `fst tw = t` unfolding seq_hoare_valid2_def by blast }
  ultimately show "Q tw'"
    by auto
qed

lemma lift_world_trans_worldline_upd2:
  assumes "tw, Bassign_trans sig exp dly \<Rightarrow>\<^sub>s tw'"
  assumes "0 < dly"
  shows "tw' = tw[sig, dly :=\<^sub>2 beval_world_raw2 tw exp]"
  using assms
proof transfer'
  fix tw tw' :: "nat \<times> 'a worldline"
  fix sig
  fix exp :: "'a bexp"
  fix dly
  assume "tw, Bassign_trans sig exp dly \<Rightarrow>\<^sub>s tw'"
  assume "0 < dly"
  obtain t \<sigma> \<gamma> \<theta> \<tau> where "destruct_worldline tw = (t, \<sigma>, \<gamma>, \<theta>, \<tau>)"
    by (meson destruct_worldline_def)
  hence "fst tw = t" and w_def: "tw = worldline2 t \<sigma> \<theta> \<tau> " and "context_invariant t \<sigma> \<gamma> \<theta> \<tau>"
    by(auto dest!: worldline2_constructible)
  hence "\<forall>i<fst tw. \<tau> i = 0"
    unfolding context_invariant_def by auto
  obtain \<tau>' where "t , \<sigma> , \<gamma> , \<theta> \<turnstile> <Bassign_trans sig exp dly, \<tau>> \<longrightarrow>\<^sub>s \<tau>'"
    and "\<tau>' = trans_post_raw sig (beval_raw t \<sigma> \<gamma> \<theta> exp) (\<sigma> sig) \<tau> t dly"
    by auto
  moreover have "beval_raw t \<sigma> \<gamma> \<theta> exp = beval_world_raw2 tw exp"
    using `tw = worldline2 t \<sigma> \<theta> \<tau> ` and `context_invariant t \<sigma> \<gamma> \<theta> \<tau>`
    by (simp add: beval_beval_world_raw_ci beval_world_raw2_def worldline2_def)
  ultimately have \<tau>'_def: "\<tau>' = trans_post_raw sig (beval_world_raw2 tw exp) (\<sigma> sig) \<tau> t dly"
    by auto
  hence \<tau>'_def': "\<tau>' = trans_post_raw sig (beval_world_raw (snd tw) (fst tw) exp) (\<sigma> sig) \<tau> (fst tw) dly"
    unfolding beval_world_raw2_def  using \<open>fst tw = t\<close> by blast
  have "tw' = (worldline2 t \<sigma> \<theta> \<tau>')"
    using `tw, Bassign_trans sig exp dly \<Rightarrow>\<^sub>s tw'` `destruct_worldline tw = (t, \<sigma>, \<gamma>, \<theta>, \<tau>)`
    unfolding world_seq_exec_def  using \<open>t , \<sigma> , \<gamma> , \<theta> \<turnstile> <Bassign_trans sig exp dly , \<tau>> \<longrightarrow>\<^sub>s \<tau>'\<close>
    by auto
  also have "... = tw[sig, dly:=\<^sub>2 beval_world_raw2 tw exp]"
    using w_def \<tau>'_def' `0 < dly` lift_trans_post_worldline_upd[where \<sigma>="\<sigma>" and t="fst tw" and \<tau>="\<tau>", OF _ \<tau>'_def']
    `\<forall>i<fst tw. \<tau> i = 0` 
    by (simp add: beval_world_raw2_def worldline2_def worldline_upd2_def)
  finally show "tw' = tw[sig, dly:=\<^sub>2 beval_world_raw2 tw exp]"
    using `fst tw = t` by auto
qed

lemma Bassign_trans_sound_hoare2:
  "0 < dly \<Longrightarrow> \<turnstile> [P] Bassign_trans sig exp dly [Q] \<Longrightarrow> \<Turnstile> [P] Bassign_trans sig exp dly [Q]"
  unfolding seq_hoare_valid2_def
proof rule+
  fix tw tw' :: "nat \<times> 'a worldline"
  assume "0 < dly"
  assume "\<turnstile> [P] Bassign_trans sig exp dly [Q]"
  hence imp: "\<forall>tw. P tw \<longrightarrow> Q( tw[sig, dly :=\<^sub>2 beval_world_raw2 tw exp])"
    by (auto dest!: BassignE_hoare2)
  assume " P tw \<and> (tw, Bassign_trans sig exp dly \<Rightarrow>\<^sub>s tw')"
  hence "P tw" and "tw, Bassign_trans sig exp dly \<Rightarrow>\<^sub>s tw'" by auto
  obtain t \<sigma> \<gamma> \<theta> \<tau> where "destruct_worldline tw = (t, \<sigma>, \<gamma>, \<theta>, \<tau>)" and "fst tw = t"
    by (metis (no_types, lifting) destruct_worldline_def)
  obtain \<tau>' where "t , \<sigma> , \<gamma> , \<theta> \<turnstile> <Bassign_trans sig exp dly, \<tau>> \<longrightarrow>\<^sub>s \<tau>'"
    by auto
  hence "tw' = worldline2 t \<sigma> \<theta> \<tau>'"
    using `tw, Bassign_trans sig exp dly \<Rightarrow>\<^sub>s tw'` `destruct_worldline tw = (t, \<sigma>, \<gamma>, \<theta>, \<tau>)`
    unfolding world_seq_exec_def  using \<open>t , \<sigma> , \<gamma> , \<theta> \<turnstile> <Bassign_trans sig exp dly , \<tau>> \<longrightarrow>\<^sub>s \<tau>'\<close> by auto
  hence "fst tw' = t"
    by transfer'  auto
  have "tw' = tw[sig, dly :=\<^sub>2 beval_world_raw2 tw exp]"
    unfolding `tw' = worldline2 t \<sigma> \<theta> \<tau>'` using `fst tw = t` `0 < dly`
    by (metis \<open>tw' = worldline2 t \<sigma> \<theta> \<tau>'\<close> \<open>tw , Bassign_trans sig exp dly \<Rightarrow>\<^sub>s tw'\<close>
    lift_world_trans_worldline_upd2)
  with imp and `P tw` have "Q(tw[sig, dly :=\<^sub>2 beval_world_raw2 tw exp])"
    using `fst tw = t` by blast
  thus "Q tw'"
    using `tw' = tw[sig, dly :=\<^sub>2 beval_world_raw2 tw exp]`
    `fst tw = t` surjective_pairing[of "tw'"]  `fst tw' = t` by auto
qed

lemma lift_world_inert_worldline_upd2:
  assumes "tw, Bassign_inert sig exp dly \<Rightarrow>\<^sub>s tw'"
  assumes "0 < dly"
  shows "tw' = tw\<lbrakk>sig, dly :=\<^sub>2 beval_world_raw2 tw exp\<rbrakk>"
  using assms
proof -
  assume "tw, Bassign_inert sig exp dly \<Rightarrow>\<^sub>s tw'"
  assume "0 < dly"
  obtain t \<sigma> \<gamma> \<theta> \<tau> where "destruct_worldline tw = (t, \<sigma>, \<gamma>, \<theta>, \<tau>)"
    by (meson destruct_worldline_def)
  hence "fst tw = t" and w_def: "tw = worldline2 t \<sigma> \<theta> \<tau> " and "context_invariant t \<sigma> \<gamma> \<theta> \<tau>"
    by(auto dest!: worldline2_constructible)
  obtain \<tau>' where "t , \<sigma> , \<gamma> , \<theta> \<turnstile> <Bassign_inert sig exp dly, \<tau>> \<longrightarrow>\<^sub>s \<tau>'"
    and "\<tau>' = inr_post_raw sig (beval_raw t \<sigma> \<gamma> \<theta> exp) (\<sigma> sig) \<tau> t dly"
    by auto
  moreover have "beval_raw t \<sigma> \<gamma> \<theta> exp = beval_world_raw2 tw exp"
    using `tw = worldline2 t \<sigma> \<theta> \<tau> ` and `context_invariant t \<sigma> \<gamma> \<theta> \<tau>`
    by (simp add: beval_beval_world_raw_ci beval_world_raw2_def worldline2_def)
  ultimately have \<tau>'_def: "\<tau>' = inr_post_raw sig (beval_world_raw2 tw exp) (\<sigma> sig) \<tau> t dly"
    by auto
  have "non_stuttering (to_trans_raw_sig \<tau>) \<sigma> sig"
    using destruct_worldline_ensure_non_stuttering[OF `destruct_worldline tw = (t, \<sigma>, \<gamma>, \<theta>, \<tau>)`]
    by auto
  have "tw' = (worldline2 t \<sigma> \<theta> \<tau>')"
    using `tw, Bassign_inert sig exp dly \<Rightarrow>\<^sub>s tw'` `destruct_worldline tw = (t, \<sigma>, \<gamma>, \<theta>, \<tau>)`
    unfolding world_seq_exec_def  using \<open>t , \<sigma> , \<gamma> , \<theta> \<turnstile> <Bassign_inert sig exp dly , \<tau>> \<longrightarrow>\<^sub>s \<tau>'\<close>
    by auto
  also have "... = tw\<lbrakk>sig, dly:=\<^sub>2 beval_world_raw2 tw exp\<rbrakk>"
    using `tw = worldline2 t \<sigma> \<theta> \<tau>` `context_invariant t \<sigma> \<gamma> \<theta> \<tau>`
    `t , \<sigma> , \<gamma> , \<theta> \<turnstile> <Bassign_inert sig exp dly, \<tau>> \<longrightarrow>\<^sub>s \<tau>'` `0 < dly`
    lift_inr_post_worldline_upd[OF _ _ `t , \<sigma> , \<gamma> , \<theta> \<turnstile> <Bassign_inert sig exp dly, \<tau>> \<longrightarrow>\<^sub>s \<tau>'` _
    `non_stuttering (to_trans_raw_sig \<tau>) \<sigma> sig`]
    by (smt \<open>fst tw = t\<close> \<open>t , \<sigma> , \<gamma> , \<theta> \<turnstile> exp \<longrightarrow>\<^sub>b beval_world_raw2 tw exp\<close> beval_beval_world_raw_ci
    snd_conv worldline2_def worldline_inert_upd2_def)
  finally show ?thesis
    using `fst tw = t` by auto
qed

lemma Bassign_inert_sound_hoare2:
  assumes "0 < dly"
  shows "\<turnstile> [P] Bassign_inert sig exp dly [Q] \<Longrightarrow> \<Turnstile> [P] Bassign_inert sig exp dly [Q]"
  unfolding seq_hoare_valid2_def
proof rule+
  fix tw tw' :: "nat \<times> 'a worldline"
  assume "\<turnstile> [P] Bassign_inert sig exp dly [Q]"
  hence imp: "\<forall>tw. P tw \<longrightarrow> Q(tw \<lbrakk>sig, dly :=\<^sub>2 beval_world_raw2 tw exp\<rbrakk>)"
    by (auto dest!: Bassign_inertE_hoare2)
  assume "P tw \<and> (tw, Bassign_inert sig exp dly \<Rightarrow>\<^sub>s tw')"
  hence "P tw" and "tw, (Bassign_inert sig exp dly) \<Rightarrow>\<^sub>s tw'" by auto
  obtain t \<sigma> \<gamma> \<theta> \<tau> where "destruct_worldline tw = (t, \<sigma>, \<gamma>, \<theta>, \<tau>)" and "fst tw = t"
    by (metis (no_types, lifting) destruct_worldline_def)
  obtain \<tau>' where "t , \<sigma> , \<gamma> , \<theta> \<turnstile> <Bassign_inert sig exp dly, \<tau>> \<longrightarrow>\<^sub>s \<tau>'"
    by auto
  hence "tw' = (worldline2 t \<sigma> \<theta> \<tau>')"
    using `tw, Bassign_inert sig exp dly \<Rightarrow>\<^sub>s tw'` `destruct_worldline tw = (t, \<sigma>, \<gamma>, \<theta>, \<tau>)`
    unfolding world_seq_exec_def  using \<open>t , \<sigma> , \<gamma> , \<theta> \<turnstile> <Bassign_inert sig exp dly , \<tau>> \<longrightarrow>\<^sub>s \<tau>'\<close> by auto
  hence "fst tw' = t"
    by transfer' auto
  have "tw' = tw\<lbrakk>sig, dly :=\<^sub>2 beval_world_raw2 tw exp\<rbrakk>"
    by (metis \<open>fst tw = t\<close> \<open>tw , Bassign_inert sig exp dly \<Rightarrow>\<^sub>s tw'\<close> assms lift_world_inert_worldline_upd2)
  with imp and `P tw` have "Q(tw\<lbrakk>sig, dly :=\<^sub>2 beval_world_raw2 tw exp\<rbrakk>)"
    using `fst tw = t` by blast
  thus "Q tw'"
    using `tw' = tw \<lbrakk> sig, dly :=\<^sub>2 beval_world_raw2 tw exp\<rbrakk>` `fst tw = t` `fst tw' = t`
    surjective_pairing[of "tw'"] by auto
qed

subsubsection \<open>Soundness and completeness\<close>

lemma soundness_hoare2:
  assumes "\<turnstile> [P] s [R]"
  assumes "nonneg_delay s"
  shows "\<Turnstile> [P] s [R]"
  using assms
proof (induction rule:seq_hoare2.induct)
  case (AssignI2 P sig dly exp)
  hence "0 < dly" by auto
  then show ?case
    using Bassign_inert_sound_hoare2[OF `0 < dly`]  using seq_hoare2.AssignI2 by fastforce
next
  case (Conseq2 P' P s Q Q')
  then show ?case by (metis seq_hoare_valid2_def)
next
  case (Conj P s Q1 Q2)
  then show ?case by (simp add: seq_hoare_valid2_def)
qed (auto simp add: Bnull_sound_hoare2 Bassign_trans_sound_hoare2 Bcomp_hoare_valid' Bguarded_hoare_valid2)

lemma  world_seq_exec_bnull:
  "tw, Bnull \<Rightarrow>\<^sub>s tw"
  unfolding world_seq_exec_def Let_def
  by (auto split:prod.splits dest!:worldline2_constructible)

lemma world_seq_exec_comp:
  assumes "nonneg_delay (Bcomp ss1 ss2)"
  shows "tw, (Bcomp ss1 ss2) \<Rightarrow>\<^sub>s (world_seq_exec (world_seq_exec tw ss1) ss2)"
proof -
  obtain t \<sigma> \<gamma> \<theta> \<tau> \<tau>' where des1: "destruct_worldline tw = (t, \<sigma>, \<gamma>, \<theta>, \<tau>)" and
    "t, \<sigma>, \<gamma>, \<theta> \<turnstile> <Bcomp ss1 ss2, \<tau>> \<longrightarrow>\<^sub>s \<tau>'" and ci1: "context_invariant t \<sigma> \<gamma> \<theta> \<tau>"
    using destruct_worldline_exist worldline2_constructible by metis
  have "\<forall>s. non_stuttering (to_trans_raw_sig \<tau>) \<sigma> s"
    using destruct_worldline_ensure_non_stuttering[OF des1] by auto
  then obtain \<tau>'' where "t, \<sigma>, \<gamma>, \<theta> \<turnstile> <ss1, \<tau>> \<longrightarrow>\<^sub>s \<tau>''" and exec1: "t, \<sigma>, \<gamma>, \<theta> \<turnstile> <ss2, \<tau>''> \<longrightarrow>\<^sub>s \<tau>'"
    and ci2: "context_invariant t \<sigma> \<gamma> \<theta> \<tau>''" using b_seq_exec_preserves_context_invariant
    using assms \<open>t , \<sigma> , \<gamma> , \<theta> \<turnstile> <Bcomp ss1 ss2 , \<tau>> \<longrightarrow>\<^sub>s \<tau>'\<close> ci1 by fastforce
  hence "\<forall>s. non_stuttering (to_trans_raw_sig \<tau>'') \<sigma> s"
    using b_seq_exec_preserves_non_stuttering 
    by (metis \<open>\<forall>s. non_stuttering (to_trans_raw_sig \<tau>) \<sigma> s\<close> assms ci1 context_invariant_def
    nonneg_delay.simps(2))
  hence *: "worldline2 t \<sigma> \<theta> \<tau>'' = world_seq_exec tw ss1"
    unfolding world_seq_exec_def Let_def using des1 by (simp add: \<open>t , \<sigma> , \<gamma> , \<theta> \<turnstile> <ss1 , \<tau>> \<longrightarrow>\<^sub>s \<tau>''\<close>)
  obtain \<theta>2 \<tau>2 \<tau>3 where des2: "destruct_worldline (worldline2 t \<sigma> \<theta> \<tau>'') = (t, \<sigma>, \<gamma>, \<theta>2, \<tau>2)" and
    beh_same:"\<And>s k. signal_of False \<theta> s k = signal_of False \<theta>2 s k" and
    trans_same: "\<And>s k. signal_of (\<sigma> s) \<tau>'' s k = signal_of (\<sigma> s) \<tau>2 s k" and
    exec2: "t, \<sigma>, \<gamma>, \<theta>2 \<turnstile> <ss2, \<tau>2> \<longrightarrow>\<^sub>s \<tau>3"
    using destruct_worldline_correctness[OF ci2]  by (metis prod.exhaust_sel)
  have "\<forall>s. non_stuttering (to_trans_raw_sig \<tau>2) \<sigma> s"
    using destruct_worldline_ensure_non_stuttering[OF des2] by blast
  have ci3: "context_invariant t \<sigma> \<gamma> \<theta>2 \<tau>2"
    using worldline2_constructible[OF des2] by auto
  have "\<And>s k. signal_of (\<sigma> s) \<tau>' s k = signal_of (\<sigma> s) \<tau>3 s k"
    using helper'[OF exec1 beh_same trans_same exec2] ci2 ci3 
    `\<forall>s. non_stuttering (to_trans_raw_sig \<tau>'') \<sigma> s` `\<forall>s. non_stuttering (to_trans_raw_sig \<tau>2) \<sigma> s`
    unfolding context_invariant_def using assms by auto
  hence "worldline2 t \<sigma> \<theta> \<tau>' = worldline2 t \<sigma> \<theta>2 \<tau>3"
    using beh_same unfolding worldline2_def worldline_raw_def
    by simp
  also have "... = world_seq_exec (worldline2 t \<sigma> \<theta> \<tau>'') ss2"
    using des2 `t, \<sigma>, \<gamma>, \<theta>2 \<turnstile> <ss2, \<tau>2> \<longrightarrow>\<^sub>s \<tau>3` unfolding world_seq_exec_def Let_def
    by auto
  finally have "worldline2 t \<sigma> \<theta> \<tau>' = world_seq_exec (worldline2 t \<sigma> \<theta> \<tau>'') ss2"
    by auto
  thus ?thesis
    using des1 `t, \<sigma>, \<gamma>, \<theta> \<turnstile> <Bcomp ss1 ss2, \<tau>> \<longrightarrow>\<^sub>s \<tau>'` unfolding  *
    world_seq_exec_def Let_def by auto
qed

lemma world_seq_exec_guarded:
  fixes tw :: "nat \<times> 'a worldline"
  assumes "beval_world_raw2 tw g"
  shows "world_seq_exec tw (Bguarded g ss1 ss2) = world_seq_exec tw ss1"
proof -
  obtain t \<sigma> \<gamma> \<theta> \<tau> \<tau>' where des1: "destruct_worldline tw = (t, \<sigma>, \<gamma>, \<theta>, \<tau>)" and
    "t, \<sigma>, \<gamma>, \<theta> \<turnstile> <Bguarded g ss1 ss2, \<tau>> \<longrightarrow>\<^sub>s \<tau>'" and ci1: "context_invariant t \<sigma> \<gamma> \<theta> \<tau>" and
    "tw = worldline2 t \<sigma> \<theta> \<tau>" and "fst tw = t" using destruct_worldline_exist worldline2_constructible
    by (metis (no_types, lifting) destruct_worldline_def)
  moreover have "beval_raw t \<sigma> \<gamma> \<theta> g"
    using assms `tw = worldline2 t \<sigma> \<theta> \<tau>` ci1  `fst tw = t`
    by (metis beval_beval_world_raw_ci beval_world_raw2_def snd_conv worldline2_def)
  ultimately have "t, \<sigma>, \<gamma>, \<theta> \<turnstile> <ss1, \<tau>> \<longrightarrow>\<^sub>s \<tau>'"
    by auto
  thus ?thesis
    by (metis (no_types, lifting) \<open>t , \<sigma> , \<gamma> , \<theta> \<turnstile> <Bguarded g ss1 ss2 , \<tau>> \<longrightarrow>\<^sub>s \<tau>'\<close> case_prod_conv
        des1 world_seq_exec_def)
qed

lemma world_seq_exec_guarded_not:
  fixes tw :: "nat \<times> 'a worldline"
  assumes "\<not> beval_world_raw2 tw g"
  shows "world_seq_exec tw (Bguarded g ss1 ss2) = world_seq_exec tw ss2"
proof -
  obtain t \<sigma> \<gamma> \<theta> \<tau> \<tau>' where des1: "destruct_worldline tw = (t, \<sigma>, \<gamma>, \<theta>, \<tau>)" and
    "t, \<sigma>, \<gamma>, \<theta> \<turnstile> <Bguarded g ss1 ss2, \<tau>> \<longrightarrow>\<^sub>s \<tau>'" and ci1: "context_invariant t \<sigma> \<gamma> \<theta> \<tau>" and
    "tw = worldline2 t \<sigma> \<theta> \<tau>" and "fst tw = t" using destruct_worldline_exist worldline2_constructible
    by (metis (no_types, lifting) destruct_worldline_def fst_def snd_def)
  moreover have "\<not> beval_raw t \<sigma> \<gamma> \<theta> g"
    using assms `tw = worldline2 t \<sigma> \<theta> \<tau>` ci1  using `fst tw = t`
    by (metis beval_beval_world_raw_ci beval_world_raw2_def snd_conv worldline2_def)
  ultimately have "t, \<sigma>, \<gamma>, \<theta> \<turnstile> <ss2, \<tau>> \<longrightarrow>\<^sub>s \<tau>'"
    by auto
  thus ?thesis
    by (metis (no_types, lifting) \<open>t , \<sigma> , \<gamma> , \<theta> \<turnstile> <Bguarded g ss1 ss2 , \<tau>> \<longrightarrow>\<^sub>s \<tau>'\<close> case_prod_conv
        des1 world_seq_exec_def)
qed

definition wp :: "'signal seq_stmt \<Rightarrow> 'signal assn2 \<Rightarrow> 'signal assn2" where
  "wp ss Q = (\<lambda>tw. \<forall>tw'. (tw, ss \<Rightarrow>\<^sub>s tw') \<longrightarrow> Q tw')"

lemma wp_bnull:
  "wp Bnull Q = Q"
  by (rule ext)(auto simp add: wp_def world_seq_exec_bnull)

lemma wp_bcomp:
  "nonneg_delay (Bcomp ss1 ss2) \<Longrightarrow> wp (Bcomp ss1 ss2) Q = wp ss1 (wp ss2 Q)"
  by (rule ext) (auto simp add: wp_def world_seq_exec_comp)

lemma wp_guarded:
  "wp (Bguarded g ss1 ss2) Q =
  (\<lambda>tw. if beval_world_raw2 tw g then wp ss1 Q tw else wp ss2 Q tw)"
  by (rule ext) (auto simp add: wp_def world_seq_exec_guarded world_seq_exec_guarded_not)

lemma wp_trans:
  "0 < dly \<Longrightarrow> wp (Bassign_trans sig exp dly) Q = (\<lambda>tw. Q(tw [sig, dly :=\<^sub>2 beval_world_raw2 tw exp]))"
  by (rule ext, metis (full_types) lift_world_trans_worldline_upd2 wp_def)

lemma wp_inert:
  "0 < dly \<Longrightarrow> wp (Bassign_inert sig exp dly) Q = (\<lambda>tw. Q(tw \<lbrakk> sig, dly :=\<^sub>2 beval_world_raw2 tw exp \<rbrakk>))"
  by (rule ext, metis lift_world_inert_worldline_upd2 wp_def)

lemma wp_is_pre: "nonneg_delay ss \<Longrightarrow> \<turnstile> [wp ss Q] ss [Q]"
proof (induction ss arbitrary: Q)
case (Bcomp ss1 ss2)
  then show ?case by (auto simp add: wp_bcomp)
next
  case (Bguarded x1 ss1 ss2)
  then show ?case by (auto intro:Conseq2 simp add: wp_guarded)
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

definition event_of :: "nat \<times> 'signal worldline  \<Rightarrow> 'signal event" where
  "event_of tw = (fst o snd o snd) (destruct_worldline tw)"

lemma event_of_alt_def1:
  "0 < fst tw \<Longrightarrow> event_of tw = {s. snd tw s (fst tw) \<noteq> snd tw s (fst tw - 1)}"
proof-
  assume "0 < fst tw"
  obtain t \<sigma> \<gamma> \<theta> \<tau> where des: "destruct_worldline tw = (t, \<sigma>, \<gamma>, \<theta>, \<tau>)"
    using prod_cases5 by blast
  hence "event_of tw = \<gamma>"
    unfolding event_of_def by auto
  also have "... = {s. \<sigma> s \<noteq> signal_of False \<theta> s (t - 1)}"
    using \<open>destruct_worldline tw = (t, \<sigma>, \<gamma>, \<theta>, \<tau>)\<close> unfolding destruct_worldline_def Let_def 
    by auto
  finally have "event_of tw = {s. \<sigma> s \<noteq> signal_of False \<theta> s (t - 1)}"
    by auto
  have "\<And>s. \<sigma> s = snd tw s (fst tw)"
    using des unfolding destruct_worldline_def Let_def by auto
  have \<theta>_def: "\<theta> = derivative_hist_raw (snd tw) (get_time tw)" and t_def: "t = fst tw"
    using des unfolding destruct_worldline_def Let_def by auto
  have "\<And>s. signal_of False \<theta> s (t - 1) = snd tw s (fst tw - 1)"
    using \<open>0 < fst tw\<close> unfolding \<theta>_def t_def by (intro  signal_of_derivative_hist_raw) simp
  thus ?thesis
    using \<open>\<And>s. \<sigma> s = snd tw s (get_time tw)\<close> \<open>event_of tw = {s. \<sigma> s \<noteq> signal_of False \<theta> s (t - 1)}\<close>
    by auto
qed

lemma event_of_alt_def2:
  "fst tw = 0 \<Longrightarrow> event_of tw = {s. snd tw s (fst tw) \<noteq> False}"
proof -
  assume "fst tw = 0"
  obtain t \<sigma> \<gamma> \<theta> \<tau> where des: "destruct_worldline tw = (t, \<sigma>, \<gamma>, \<theta>, \<tau>)"
    using prod_cases5 by blast
  hence "event_of tw = \<gamma>"
    unfolding event_of_def by auto
  also have "... = {s. \<sigma> s \<noteq> signal_of False \<theta> s (t - 1)}"
    using \<open>destruct_worldline tw = (t, \<sigma>, \<gamma>, \<theta>, \<tau>)\<close> unfolding destruct_worldline_def Let_def 
    by auto
  finally have "event_of tw = {s. \<sigma> s \<noteq> signal_of False \<theta> s (t - 1)}"
    by auto
  have "\<And>s. \<sigma> s = snd tw s (fst tw)"
    using des unfolding destruct_worldline_def Let_def by auto
  have \<theta>_def: "\<theta> = derivative_hist_raw (snd tw) (get_time tw)" and t_def: "t = fst tw"
    using des unfolding destruct_worldline_def Let_def by auto
  have "\<And>s. signal_of False \<theta> s (t - 1) = False"
    using \<open>fst tw = 0\<close> unfolding \<theta>_def t_def 
    by (metis derivative_hist_raw_def diff_0_eq_0 le_numeral_extra(3) signal_of_zero zero_option_def)
  thus ?thesis
    using \<open>\<And>s. \<sigma> s = snd tw s (get_time tw)\<close> \<open>event_of tw = {s. \<sigma> s \<noteq> signal_of False \<theta> s (t - 1)}\<close> 
    by auto
qed

lemma event_of_alt_def:
  "event_of tw = (if fst tw = 0 then {s. snd tw s (fst tw) \<noteq> False} else 
                                     {s. snd tw s (fst tw) \<noteq> snd tw s (fst tw - 1)})"
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

lemma strengthen_pre_conc_hoare:
  assumes "\<forall>w. P' w \<longrightarrow> P w" and "\<turnstile> \<lbrace>P\<rbrace> s \<lbrace>Q\<rbrace>"
  shows "\<turnstile> \<lbrace>P'\<rbrace> s \<lbrace>Q\<rbrace>"
  using assms by (blast intro: Conseq')

definition world_conc_exec :: "nat \<times> 'signal worldline \<Rightarrow> 'signal conc_stmt \<Rightarrow> nat \<times> 'signal worldline"
  where
  "world_conc_exec tw c = (let (t, \<sigma>, \<gamma>, \<theta>, \<tau>) = destruct_worldline tw;
                                            \<tau>' = b_conc_exec t \<sigma> \<gamma> \<theta> c \<tau>
                           in worldline2 t \<sigma> \<theta> \<tau>')"

abbreviation world_conc_exec_abb :: "nat \<times> 'signal worldline \<Rightarrow> 'signal conc_stmt \<Rightarrow> nat \<times> 'signal worldline \<Rightarrow> bool"
  ("(_ , _) \<Rightarrow>\<^sub>c _")
  where "world_conc_exec_abb tw s w' \<equiv> (world_conc_exec tw s = w')"

(* Diagram for lifting the concurrent execution to the worldline level
 *
 *         w, t                    \<Rightarrow>\<^sub>c          w', t
 *           \<down>                                  \<up>
 *   destruct_worldline                      worldline2 t \<sigma> \<theta> \<tau>'
 *           \<down>                                  \<up>
 *         t, \<sigma>, \<gamma>, \<theta> \<turnstile> <c, \<tau>>    \<longrightarrow>\<^sub>c          \<tau>'
 *
 *)

lemma fst_world_conc_exec:
  assumes "tw, cs \<Rightarrow>\<^sub>c tw'"
  shows "fst tw = fst tw'"
proof -
  have "tw' = world_conc_exec tw cs"
    using assms by auto
  obtain t \<sigma> \<gamma> \<theta> \<tau> where "destruct_worldline tw = (t, \<sigma>, \<gamma>, \<theta>, \<tau>)"
    using destruct_worldline_exist by blast
  obtain \<tau>' where "\<tau>' = b_conc_exec t \<sigma> \<gamma> \<theta> cs \<tau>"
    by auto
  have "fst tw = t"
    using fst_destruct_worldline `destruct_worldline tw = (t, \<sigma>, \<gamma>, \<theta>, \<tau>)`  by (metis fst_conv)
  have "fst tw' = fst (worldline2 t \<sigma> \<theta> \<tau>')"
    using `tw' = world_conc_exec tw cs` `destruct_worldline tw = (t, \<sigma>, \<gamma>, \<theta>, \<tau>)`
    unfolding world_conc_exec_def by auto
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
  obtain t \<sigma> \<gamma> \<theta> \<tau> \<tau>' where "destruct_worldline tw = (t, \<sigma>, \<gamma>, \<theta>, \<tau>)" and
    "t, \<sigma>, \<gamma>, \<theta> \<turnstile> <cs1 || cs2, \<tau>> \<longrightarrow>\<^sub>c \<tau>'" and "worldline2 t \<sigma> \<theta> \<tau>' = tw1"
    using assms(1) unfolding world_conc_exec_def Let_def by (auto split:prod.splits)
  hence "t, \<sigma>, \<gamma>, \<theta> \<turnstile> <cs2 || cs1, \<tau>> \<longrightarrow>\<^sub>c \<tau>'"
    using parallel_comp_commute'[OF assms(3)] by auto
  thus ?thesis
    using assms(2) unfolding world_conc_exec_def Let_def
    using \<open>destruct_worldline tw = (t, \<sigma>, \<gamma>, \<theta>, \<tau>)\<close> \<open>worldline2 t \<sigma> \<theta> \<tau>' = tw1\<close>  by auto
qed

lemma world_conc_exec_disjnt:
  fixes tw :: "nat \<times> 'a worldline"
  assumes "disjnt sl (event_of tw)" shows "tw, (process sl : ss) \<Rightarrow>\<^sub>c tw"
proof -
  obtain t \<sigma> \<gamma> \<theta> \<tau> \<tau>' where des: "destruct_worldline tw = (t, \<sigma>, \<gamma>, \<theta>, \<tau>)" and
    ex: "t, \<sigma>, \<gamma>, \<theta> \<turnstile> <process sl : ss, \<tau>> \<longrightarrow>\<^sub>c \<tau>'"
    using destruct_worldline_exist by blast
  moreover have "disjnt sl \<gamma>"
    using assms unfolding event_of_def by (simp add: des)
  ultimately have "\<tau>' = \<tau>"
    by auto
  hence "worldline2 t \<sigma> \<theta> \<tau>' = tw"
    using des  worldline2_constructible by fastforce
  with des ex show ?thesis
    by (auto simp add: world_conc_exec_def split:prod.splits)
qed

lemma world_conc_exec_not_disjnt:
  fixes tw :: "nat \<times> 'a worldline"
  assumes "\<not> disjnt sl (event_of tw)" and "tw, ss \<Rightarrow>\<^sub>s tw'"
  shows "tw, (process sl : ss) \<Rightarrow>\<^sub>c tw'"
proof -
  obtain t \<sigma> \<gamma> \<theta> \<tau> \<tau>' where des: "destruct_worldline tw = (t, \<sigma>, \<gamma>, \<theta>, \<tau>)" and
    ex: "t, \<sigma>, \<gamma>, \<theta> \<turnstile> <process sl : ss, \<tau>> \<longrightarrow>\<^sub>c \<tau>'"
    using destruct_worldline_exist by blast
  moreover have "\<not> disjnt sl \<gamma>"
    using assms unfolding event_of_def des by (simp add: des)
  ultimately have "\<tau>' = b_seq_exec t \<sigma> \<gamma> \<theta> ss \<tau>"
    by auto
  hence "worldline2 t \<sigma> \<theta> \<tau>' = tw'"
    using assms(2) des by (metis (no_types, lifting) old.prod.case snd_conv world_seq_exec_def)
  thus ?thesis
    using des ex
    by (simp add: world_conc_exec_def)
qed

definition
conc_hoare_valid :: "'signal assn2 \<Rightarrow> 'signal conc_stmt \<Rightarrow> 'signal assn2 \<Rightarrow> bool" ("\<Turnstile> \<lbrace>(1_)\<rbrace>/ (_)/ \<lbrace>(1_)\<rbrace>" 50)
where "\<Turnstile> \<lbrace>P\<rbrace> c \<lbrace>Q\<rbrace> \<longleftrightarrow>  (\<forall>tw tw'.  P tw \<and> (tw, c \<Rightarrow>\<^sub>c tw') \<longrightarrow> Q tw')"

lemma helper_b_conc:
  assumes "t, \<sigma>, \<gamma>, \<theta>1 \<turnstile> <cs, \<tau>1> \<longrightarrow>\<^sub>c \<tau>1'"
  assumes "\<And>k s. signal_of False \<theta>1 s k = signal_of False \<theta>2 s k"
  assumes "\<And>k s. signal_of (\<sigma> s) \<tau>1 s k = signal_of (\<sigma> s) \<tau>2 s k"
  assumes "t, \<sigma>, \<gamma>, \<theta>2 \<turnstile> <cs, \<tau>2> \<longrightarrow>\<^sub>c \<tau>2'"
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
  define \<tau>11 where "\<tau>11 = b_conc_exec t \<sigma> \<gamma> \<theta>1 cs1 \<tau>1"
  define \<tau>12 where "\<tau>12 = b_conc_exec t \<sigma> \<gamma> \<theta>1 cs2 \<tau>1"
  hence \<tau>1'_def: "\<tau>1' = clean_zip_raw \<tau>1 (\<tau>11, set (signals_from cs1)) (\<tau>12, set (signals_from cs2))"
    using \<tau>11_def using Bpar by auto
  define \<tau>21 where "\<tau>21 = b_conc_exec t \<sigma> \<gamma> \<theta>2 cs1 \<tau>2"
  define \<tau>22 where "\<tau>22 = b_conc_exec t \<sigma> \<gamma> \<theta>2 cs2 \<tau>2"
  hence \<tau>2'_def: "\<tau>2' = clean_zip_raw \<tau>2 (\<tau>21, set (signals_from cs1)) (\<tau>22, set (signals_from cs2))"
    using \<tau>21_def using Bpar by auto
  hence ind1: "\<And>s k. signal_of (\<sigma> s) \<tau>11 s k = signal_of (\<sigma> s) \<tau>21 s k"
    using Bpar(1)[OF _ Bpar(4-5) _ Bpar(7-10), of "\<tau>11" "\<tau>21"] \<tau>11_def \<tau>21_def 
    using Bpar.prems(9) nonneg_delay_conc.simps(2)  by (simp add: Bpar.prems(10) Bpar.prems(11))
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
  have "disjnt sl \<gamma> \<or> \<not> disjnt sl \<gamma>"
    by auto
  moreover
  { assume "disjnt sl \<gamma>"
    hence "\<tau>1' = \<tau>1" and "\<tau>2' = \<tau>2"
      using Bsingle by auto
    with Bsingle(3) have ?case by auto }
  moreover
  { assume "\<not> disjnt sl \<gamma>"
    hence tau1': "t, \<sigma>, \<gamma>, \<theta>1 \<turnstile> <ss, \<tau>1> \<longrightarrow>\<^sub>s \<tau>1'" and tau2': "t, \<sigma>, \<gamma>, \<theta>2 \<turnstile> <ss, \<tau>2> \<longrightarrow>\<^sub>s \<tau>2'"
      using Bsingle by auto
    have "nonneg_delay ss"
      using Bsingle by auto
    hence ?case
      using helper'[OF tau1' Bsingle(2-3) tau2' Bsingle(5-8)] Bsingle.prems(10) Bsingle.prems(11) 
      by blast }
  ultimately show ?case by auto
qed

lemma helper_init':
  assumes "init' t \<sigma> \<gamma> \<theta>1 cs \<tau>1 = \<tau>1'"
  assumes "\<And>k s. signal_of False \<theta>1 s k = signal_of False \<theta>2 s k"
  assumes "\<And>k s. signal_of (\<sigma> s) \<tau>1 s k = signal_of (\<sigma> s) \<tau>2 s k"
  assumes "init' t \<sigma> \<gamma> \<theta>2 cs \<tau>2 = \<tau>2'"
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
  define \<tau>11 where "\<tau>11 = init' t \<sigma> \<gamma> \<theta>1 cs1 \<tau>1"
  define \<tau>12 where "\<tau>12 = init' t \<sigma> \<gamma> \<theta>1 cs2 \<tau>1"
  hence \<tau>1'_def: "\<tau>1' = clean_zip_raw \<tau>1 (\<tau>11, set (signals_from cs1)) (\<tau>12, set (signals_from cs2))"
    using \<tau>11_def using Bpar by auto
  define \<tau>21 where "\<tau>21 = init' t \<sigma> \<gamma> \<theta>2 cs1 \<tau>2"
  define \<tau>22 where "\<tau>22 = init' t \<sigma> \<gamma> \<theta>2 cs2 \<tau>2"
  hence \<tau>2'_def: "\<tau>2' = clean_zip_raw \<tau>2 (\<tau>21, set (signals_from cs1)) (\<tau>22, set (signals_from cs2))"
    using \<tau>21_def using Bpar by auto
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
  hence tau1': "t, \<sigma>, \<gamma>, \<theta>1 \<turnstile> <ss, \<tau>1> \<longrightarrow>\<^sub>s \<tau>1'" and tau2': "t, \<sigma>, \<gamma>, \<theta>2 \<turnstile> <ss, \<tau>2> \<longrightarrow>\<^sub>s \<tau>2'"
    using Bsingle by auto
  have "nonneg_delay ss"
    using Bsingle by auto
  thus ?case
    using helper'[OF tau1' Bsingle(2-3) tau2' Bsingle(5-8)] 
    by (simp add: Bsingle.prems(10) Bsingle.prems(11))
qed

lemma world_conc_exec_parallel:
  assumes "conc_stmt_wf (cs1 || cs2)" and "nonneg_delay_conc (cs1 || cs2)"
  shows "tw, (cs1 || cs2) \<Rightarrow>\<^sub>c (world_conc_exec (world_conc_exec tw cs1) cs2)"
proof -
  have "nonneg_delay_conc cs1" and "nonneg_delay_conc cs2"
    using assms by auto
  obtain t \<sigma> \<gamma> \<theta> \<tau> \<tau>' where des: "destruct_worldline tw = (t, \<sigma>, \<gamma>, \<theta>, \<tau>)" and
    ex: "t, \<sigma>, \<gamma>, \<theta> \<turnstile> <cs1, \<tau>> \<longrightarrow>\<^sub>c \<tau>'" and ci: "context_invariant t \<sigma> \<gamma> \<theta> \<tau>"
    using destruct_worldline_exist worldline2_constructible by (metis)
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
  have ci': "context_invariant t \<sigma> \<gamma> \<theta> \<tau>'"
    using b_conc_exec_preserves_context_invariant[OF ci ex `nonneg_delay_conc cs1`] by auto
  hence wcs1: "world_conc_exec tw cs1 = (worldline2 t \<sigma> \<theta> \<tau>')"
    using des ex by (simp add: world_conc_exec_def)
  obtain theta tau' where des2: "destruct_worldline (worldline2 t \<sigma> \<theta> \<tau>') = (t, \<sigma>, \<gamma>, theta, tau')"
    and beh_same: "\<And>k s. signal_of False \<theta> s k = signal_of False theta s k" and
        trans_same: "\<And>k s. signal_of (\<sigma> s) \<tau>' s k = signal_of (\<sigma> s) tau' s k"
    using destruct_worldline_correctness[OF ci'] by (metis prod_cases4)
  have "\<forall>s. non_stuttering (to_trans_raw_sig tau') \<sigma> s"
    using destruct_worldline_ensure_non_stuttering[OF des2] by auto
  have ci2: "context_invariant t \<sigma> \<gamma> theta tau'" and "worldline2 t \<sigma> \<theta> \<tau>' = worldline2 t \<sigma> theta tau'"
    using worldline2_constructible[OF des2] by auto
  have "\<And>k s. signal_of (\<sigma> s) (b_conc_exec t \<sigma> \<gamma> \<theta> cs2 \<tau>') s  k =
              signal_of  (\<sigma> s) (b_conc_exec t \<sigma> \<gamma> theta cs2 tau') s k"
    using helper_b_conc[OF _ beh_same trans_same] ci2 ci' `nonneg_delay_conc cs2` 
    unfolding context_invariant_def 
    by (simp add: \<open>\<forall>s. non_stuttering (to_trans_raw_sig \<tau>') \<sigma> s\<close> \<open>\<forall>s. non_stuttering (to_trans_raw_sig tau') \<sigma> s\<close>)
  hence *: "worldline2 t \<sigma> theta (b_conc_exec t \<sigma> \<gamma> theta cs2 tau') =
        worldline2 t \<sigma> \<theta> (b_conc_exec t \<sigma> \<gamma> \<theta> cs2 \<tau>')"
    using beh_same unfolding worldline_raw_def worldline2_def by auto
  have "b_conc_exec t \<sigma> \<gamma> \<theta> (cs1 || cs2) \<tau> =  b_conc_exec t \<sigma> \<gamma> \<theta> cs2 \<tau>'"
    using b_conc_exec_sequential[OF assms(1)] ex by auto
  hence "world_conc_exec tw (cs1 || cs2) = worldline2 t \<sigma> \<theta> (b_conc_exec t \<sigma> \<gamma> \<theta> cs2 \<tau>')"
    using des ex by (auto simp add: world_conc_exec_def)
  hence "(world_conc_exec tw cs1), cs2 \<Rightarrow>\<^sub>c (world_conc_exec tw (cs1 || cs2))"
    using des2 wcs1 *  by (simp add: world_conc_exec_def)
  thus ?thesis
    by simp
qed

lemma world_conc_exec_parallel2:
  assumes "conc_stmt_wf (cs1 || cs2)" and "nonneg_delay_conc (cs1 || cs2)"
  shows "tw, (cs1 || cs2) \<Rightarrow>\<^sub>c (world_conc_exec (world_conc_exec tw cs2) cs1)"
proof -
  have wf: "conc_stmt_wf (cs2 || cs1)" and nd: "nonneg_delay_conc (cs2 || cs1)"
    using assms unfolding conc_stmt_wf_def by auto
  have "tw, (cs1 || cs2) \<Rightarrow>\<^sub>c world_conc_exec tw (cs2 || cs1)"
    using world_conc_exec_commute[OF _ _ assms(1)] by blast
  with world_conc_exec_parallel[OF wf nd] show ?thesis
    by auto
qed

lemma parallel_valid:
  assumes "\<Turnstile> \<lbrace>P\<rbrace> c1 \<lbrace>R\<rbrace>" and "\<Turnstile> \<lbrace>R\<rbrace> c2 \<lbrace>Q\<rbrace>" and "conc_stmt_wf (c1 || c2)"
  assumes "nonneg_delay_conc (c1 || c2)"
  shows "\<Turnstile> \<lbrace>P\<rbrace> c1 || c2 \<lbrace>Q\<rbrace>"
  unfolding conc_hoare_valid_def
proof rule+
  fix tw tw':: "nat \<times> 'a worldline"
  assume "P tw \<and> tw , c1 || c2 \<Rightarrow>\<^sub>c tw'"
  hence "P tw" and "tw, c1 || c2 \<Rightarrow>\<^sub>c tw'"
    by auto
  then obtain t \<sigma> \<gamma> \<theta> \<tau> \<tau>' where des: "destruct_worldline tw = (t, \<sigma>, \<gamma>, \<theta>, \<tau>)" and
    *: "t, \<sigma>, \<gamma>, \<theta> \<turnstile> <c1 || c2, \<tau>> \<longrightarrow>\<^sub>c \<tau>'" and w'_def: "worldline2 t \<sigma> \<theta> \<tau>' = tw'" and
    ci: "context_invariant t \<sigma> \<gamma> \<theta> \<tau>"
    unfolding world_conc_exec_def Let_def  using destruct_worldline_exist
    by (auto simp add: worldline2_constructible split:prod.splits)
  have "\<And>s. non_stuttering (to_trans_raw_sig \<tau>) \<sigma> s"
    using destruct_worldline_ensure_non_stuttering[OF des] by auto
  define \<tau>1 where "\<tau>1 = b_conc_exec t \<sigma> \<gamma> \<theta> c1 \<tau>"
  hence ci1: "context_invariant t \<sigma> \<gamma> \<theta> \<tau>1"
    using b_conc_exec_preserves_context_invariant[OF ci] assms(4) by auto
  have "\<And>n. n \<le> t \<Longrightarrow> \<tau> n = 0"
    using destruct_worldline_trans_zero_upto_now[OF des] by auto
  have "\<forall>s. non_stuttering (to_trans_raw_sig \<tau>1) \<sigma> s"
  proof 
    fix s
    have "t, \<sigma>, \<gamma>, \<theta> \<turnstile> <c1, \<tau>> \<longrightarrow>\<^sub>c \<tau>1"
      unfolding \<tau>1_def by auto
    moreover have "non_stuttering (to_trans_raw_sig \<tau>) \<sigma> s"
      by (simp add: \<open>\<And>s. non_stuttering (to_trans_raw_sig \<tau>) \<sigma> s\<close>)
    moreover have "conc_stmt_wf c1" and "nonneg_delay_conc c1"
      using assms by auto
    ultimately show "non_stuttering (to_trans_raw_sig \<tau>1) \<sigma> s"
      using b_conc_exec_preserves_non_stuttering[OF _ _ `\<And>n. n \<le> t \<Longrightarrow> \<tau> n = 0`]
      by auto
  qed
  define \<tau>2 where "\<tau>2 = b_conc_exec t \<sigma> \<gamma> \<theta> c2 \<tau>"
  hence ci2: "context_invariant t \<sigma> \<gamma> \<theta> \<tau>2"
    using b_conc_exec_preserves_context_invariant[OF ci] assms(4) by auto
  have \<tau>'_def: "\<tau>' = b_conc_exec t \<sigma> \<gamma> \<theta> c2 \<tau>1"
    using b_conc_exec_sequential[OF assms(3)] * unfolding \<tau>1_def by auto
  define tw1 where "tw1 = worldline2 t \<sigma> \<theta> \<tau>1"
  have "tw, c1 \<Rightarrow>\<^sub>c tw1"
    using des \<tau>1_def unfolding world_conc_exec_def Let_def by (simp add: tw1_def)
  hence "R tw1"
    using assms(1) `P tw` unfolding conc_hoare_valid_def by blast
  obtain theta1 tau1 where des2: "destruct_worldline tw1 = (t, \<sigma>, \<gamma>, theta1, tau1)" and
    beh_same: "\<And>k s. signal_of False \<theta> s k = signal_of False theta1 s k" and
    trans_same: "\<And>k s. signal_of (\<sigma> s) \<tau>1 s k = signal_of (\<sigma> s) tau1 s k"
    using destruct_worldline_exist[of "worldline2 t \<sigma> \<theta> \<tau>1"] unfolding tw1_def
    using destruct_worldline_correctness[OF ci1] by metis
  have "\<forall>s. non_stuttering (to_trans_raw_sig tau1) \<sigma> s"
    using destruct_worldline_ensure_non_stuttering[OF des2]
    by auto
  have "context_invariant t \<sigma> \<gamma> theta1 tau1"
    using des2 worldline2_constructible by fastforce
  moreover have "nonneg_delay_conc c2"
    using assms(4) by auto
  ultimately have "worldline2 t \<sigma> theta1 (b_conc_exec t \<sigma> \<gamma> theta1 c2 tau1) = worldline2 t \<sigma> \<theta> \<tau>'"
    using beh_same trans_same \<tau>'_def ci1  
  proof -
    have "\<And>k s. signal_of (\<sigma> s) (b_conc_exec t \<sigma> \<gamma> theta1 c2 tau1) s k =
          signal_of (\<sigma> s) (b_conc_exec t \<sigma> \<gamma> \<theta> c2 \<tau>1) s k"
      using helper_b_conc[OF _ beh_same trans_same] `context_invariant t \<sigma> \<gamma> theta1 tau1` 
      ci1 `\<forall>s. non_stuttering (to_trans_raw_sig \<tau>1) \<sigma> s` `\<forall>s. non_stuttering (to_trans_raw_sig tau1) \<sigma> s`
      unfolding context_invariant_def   by (simp add: \<open>nonneg_delay_conc c2\<close>)
    thus ?thesis
      unfolding worldline2_def worldline_raw_def \<tau>'_def  using beh_same by auto
  qed
  hence "tw1, c2 \<Rightarrow>\<^sub>c tw'"
    using des2 by (simp add: w'_def world_conc_exec_def)
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
  { fix tw  tw' :: "nat \<times> 'a worldline"
    assume as: "P tw \<and> (tw ,  process sl : ss \<Rightarrow>\<^sub>c tw')"
    then obtain t \<sigma> \<gamma> \<theta> \<tau> \<tau>' where des: "destruct_worldline tw = (t, \<sigma>, \<gamma>, \<theta>, \<tau>)" and "P tw" and
      ex: "t, \<sigma>, \<gamma>, \<theta> \<turnstile> <process sl : ss, \<tau>> \<longrightarrow>\<^sub>c \<tau>'" and "(worldline2 t \<sigma> \<theta> \<tau>') = tw'"
      unfolding world_seq_exec_def Let_def
      by (metis (mono_tags, lifting) case_prod_beta' prod.exhaust_sel world_conc_exec_def)
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
        using \<open>destruct_worldline tw = (t, \<sigma>, \<gamma>, \<theta>, \<tau>)\<close> \<open>(worldline2 t \<sigma> \<theta> \<tau>') = tw'\<close> worldline2_constructible
        by (metis)
      with Single have "Q tw'"
        unfolding event_of_def  using \<open>P tw \<and> tw, process sl : ss \<Rightarrow>\<^sub>c tw'\<close>
        \<open>destruct_worldline tw = (t, \<sigma>, \<gamma>, \<theta>, \<tau>)\<close> \<open>disjnt sl \<gamma>\<close>  disjnt_sym by fastforce }
    moreover
    { assume "\<not> disjnt sl \<gamma>"
      hence "\<not> disjnt sl (event_of tw)"
        unfolding event_of_def using des `fst tw = t` by auto
      moreover have "tw, ss \<Rightarrow>\<^sub>s tw'"
        using as `\<not> disjnt sl \<gamma>`
      proof -
        have "t , \<sigma> , \<gamma> , \<theta> \<turnstile> <ss , \<tau>> \<longrightarrow>\<^sub>s \<tau>'"
          using \<open>\<not> disjnt sl \<gamma>\<close> ex by force
        then show ?thesis
          by (simp add: \<open>(worldline2 t \<sigma> \<theta> \<tau>') = tw'\<close> des world_seq_exec_def)
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
    using world_conc_exec_commute[OF _ _ Parallel2(3)]  by (metis conc_hoare_valid_def)
next
  case (Conseq' P' P c Q Q')
  then show ?case by (metis conc_hoare_valid_def)
qed

definition wp_conc :: "'signal conc_stmt \<Rightarrow> 'signal assn2 \<Rightarrow> 'signal assn2" where
  "wp_conc cs Q = (\<lambda>tw. \<forall>tw'. (tw, cs \<Rightarrow>\<^sub>c tw') \<longrightarrow> Q tw')"

lemma wp_conc_single:
  "wp_conc (process sl : ss) Q =
  (\<lambda>tw. if disjnt sl (event_of tw) then Q tw else wp ss Q tw)"
  by (rule ext) (auto simp add: wp_conc_def wp_def world_conc_exec_disjnt world_conc_exec_not_disjnt)

lemma wp_conc_parallel:
  assumes "conc_stmt_wf (cs1 || cs2)" and "nonneg_delay_conc (cs1 || cs2)"
  shows "wp_conc (cs1 || cs2) Q =  wp_conc cs1 (wp_conc cs2 Q)"
  by (rule ext)(auto simp add: wp_conc_def world_conc_exec_parallel[OF assms])

lemma wp_conc_parallel2:
  assumes "conc_stmt_wf (cs1 || cs2)" and "nonneg_delay_conc (cs1 || cs2)"
  shows "wp_conc (cs1 || cs2) Q =  wp_conc cs2 (wp_conc cs1 Q)"
  by (rule ext)(auto simp add: wp_conc_def world_conc_exec_parallel2[OF assms])

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
  have "(?s1 = val \<or> ?s2 = (\<not> val)) \<or> (?s1 = (\<not> val) \<and> ?s2 = val)"
    by auto
  moreover
  { assume "?s1 = val \<or> ?s2 = (\<not> val)"
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
  { assume "?s1 = (\<not> val) \<and> ?s2 = val"
    hence "purge_raw \<tau> t dly sig def val = override_on \<tau> (\<lambda>n. (\<tau> n)(sig := None)) ({t<..<the ?k2} \<union> {the ?k2<..t + dly})"
      (is "?lhs = ?rhs") unfolding purge_raw_def Let_def by auto
    hence "?lhs(t:=0) = ?rhs(t:=0)"
      by auto
    have "t < the ?k2"
    proof -
      have "?s1 \<noteq> val" and "?s2 \<noteq> (\<not> val)"
        using `?s1 = (\<not> val) \<and> ?s2 = val` by auto
      have "\<exists>n>t. n \<le> t + dly \<and> \<tau> n sig = Some val"
        using switch_signal_ex_mapping[OF `?s1 \<noteq> val` `?s2 \<noteq> (\<not> val)`] assms
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
  assumes "context_invariant t \<sigma> \<gamma> \<theta> \<tau>"
  shows "post_necessary_raw n \<tau> t s val (\<sigma> s) \<longleftrightarrow> post_necessary_raw n (\<tau>(t:=0)) t s val (\<sigma> s)"
proof                 
  assume "post_necessary_raw n \<tau> t s val (\<sigma> s)"
  hence "(\<exists>i. i \<le> t + n \<and>  \<tau> i s = Some (\<not> val) \<and> (\<forall>j>i. j \<le> t + n \<longrightarrow>  \<tau> j s = None))
                                      \<or>   (\<forall>i. i \<le> t + n \<longrightarrow>  \<tau> i s = None) \<and> val \<noteq> (\<sigma> s)"
    (is "?case1 \<or> ?case2")
    unfolding post_necessary_raw_correctness2 by blast
  moreover
  { assume "?case1"
    then obtain i where "i \<le> t + n" and " \<tau> i s = Some (\<not> val) \<and> (\<forall>j>i. j \<le> t + n \<longrightarrow>  \<tau> j s = None) "
      by auto
    hence "t < i"
      using assms unfolding context_invariant_def  
      by (metis domI domIff not_le_imp_less zero_fun_def zero_option_def)
    hence "(\<exists>i. i \<le> t + n \<and>  (\<tau>(t:=0)) i s = Some (\<not> val) \<and> (\<forall>j>i. j \<le> t + n \<longrightarrow>  (\<tau>(t:=0)) j s = None))"
      using `i \<le> t + n` ` \<tau> i s = Some (\<not> val) \<and> (\<forall>j>i. j \<le> t + n \<longrightarrow>  \<tau> j s = None)` 
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
  hence "(\<exists>i. i \<le> t + n \<and>  (\<tau>(t:=0)) i s = Some (\<not> val) \<and> (\<forall>j>i. j \<le> t + n \<longrightarrow>  (\<tau>(t:=0)) j s = None))
                                      \<or>   (\<forall>i. i \<le> t + n \<longrightarrow>  (\<tau>(t:=0)) i s = None) \<and> val \<noteq> (\<sigma> s)"
    (is "?case1 \<or> ?case2") unfolding post_necessary_raw_correctness2 by auto
  moreover
  { assume "?case1"
    then obtain i where "i \<le> t + n" and " ((\<tau>(t:=0)) i s = Some (\<not> val) \<and> (\<forall>j>i. j \<le> t + n \<longrightarrow>  (\<tau>(t:=0)) j s = None)) "
      by auto
    hence "i \<ge> t"
      using assms unfolding context_invariant_def 
      by (metis fun_upd_triv le_refl nat_le_linear option.discI zero_fun_def zero_option_def)
    hence "i \<noteq> t"
      by (metis \<open>(\<tau>(t := 0)) i s = Some (\<not> val) \<and> (\<forall>j>i. j \<le> t + n \<longrightarrow> (\<tau>(t := 0)) j s = None)\<close>
      fun_upd_apply option.distinct(1) zero_fun_def zero_option_def)
    hence " \<tau> i s = Some (\<not> val) \<and> (\<forall>j>i. j \<le> t + n \<longrightarrow>  \<tau> j s = None)"
      using ` (\<tau>(t:=0)) i s = Some (\<not> val) \<and> (\<forall>j>i. j \<le> t + n \<longrightarrow>  (\<tau>(t:=0)) j s = None)` `i \<ge> t`
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
        by (metis (no_types, lifting) \<open>(\<forall>i\<le>t + n. (\<tau>(t := 0)) i s = None) \<and> val \<noteq> \<sigma> s\<close> assms
        context_invariant_def fun_upd_triv order_refl signal_of_def zero_option_def) }
    moreover
    { assume " \<tau> t s = Some (\<sigma> s)"
      hence "(\<exists>i. i \<le> t + n \<and>  \<tau> i s = Some (\<not> val) \<and> (\<forall>j>i. j \<le> t + n \<longrightarrow>  \<tau> j s = None))"
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
  assumes "context_invariant t \<sigma> \<gamma> \<theta> \<tau>"
  shows "context_invariant t \<sigma> \<gamma> \<theta> (purge_raw \<tau> t dly sig def val)"
proof -
  have "\<forall>n\<le>t.  \<tau> n = 0" and "\<gamma> = {s. \<sigma> s \<noteq> signal_of False \<theta> s (t - 1)}" and "\<forall>n\<ge>t.  \<theta> n = 0"
    using assms unfolding context_invariant_def by auto
  moreover hence "\<forall>n < t. (purge_raw \<tau> t dly sig def val) n = 0"
    by (simp add: purge_preserve_trans_removal)
  ultimately show ?thesis
    unfolding context_invariant_def by (metis purge_raw_before_now_unchanged)
qed

lemma b_seq_exec_mono_wrt_rem_curr_trans:
  assumes "t, \<sigma>, \<gamma>, \<theta> \<turnstile> <ss, \<tau>> \<longrightarrow>\<^sub>s \<tau>'"
  assumes "nonneg_delay ss"
  assumes "context_invariant t \<sigma> \<gamma> \<theta> \<tau>"
  shows "t, \<sigma>, \<gamma>, \<theta> \<turnstile> <ss, \<tau>(t:=0)> \<longrightarrow>\<^sub>s \<tau>'(t:=0)"
  using assms
proof (induction ss arbitrary: \<tau> \<tau>')
  case (Bcomp ss1 ss2)
  then show ?case
    using b_seq_exec_preserves_context_invariant  by (metis b_seq_exec.simps(2) nonneg_delay.simps(2))
next
  case (Bguarded x1 ss1 ss2)
  then show ?case  by auto
next
  case (Bassign_trans sig e dly)
  hence "\<tau>' = trans_post_raw sig (beval_raw t \<sigma> \<gamma> \<theta> e) (\<sigma> sig) \<tau> t dly" and "0 < dly"
    by auto
  hence "\<tau>'(t:=0) = (trans_post_raw sig (beval_raw t \<sigma> \<gamma> \<theta> e) (\<sigma> sig) \<tau> t dly)(t:=0)"
    by auto
  also have "... = trans_post_raw sig (beval_raw t \<sigma> \<gamma> \<theta> e) (\<sigma> sig) (\<tau>(t:=0)) t dly"
    using `0 < dly` post_necessary_raw_rem_curr_trans[OF `context_invariant t \<sigma> \<gamma> \<theta> \<tau>`]
    by (metis (no_types, hide_lams) Bassign_trans.prems(2) Bassign_trans.prems(3) \<open>\<tau>' =
    trans_post_raw sig (beval_raw t \<sigma> \<gamma> \<theta> e) (\<sigma> sig) \<tau> t dly\<close> b_seq_exec.simps(4)
    context_invariant_def fun_upd_triv nonneg_delay_same order_refl)
  finally show ?case
    by (metis b_seq_exec.simps(4))
next
  case (Bassign_inert sig e dly)
  hence \<tau>'_def: "\<tau>' = inr_post_raw sig (beval_raw t \<sigma> \<gamma> \<theta> e) (\<sigma> sig) \<tau> t dly" and "0 < dly"
    by auto
  have "context_invariant t \<sigma> \<gamma> \<theta> (purge_raw \<tau> t dly sig (\<sigma> sig) (beval_raw t \<sigma> \<gamma> \<theta> e))"
    using context_invariant_purged `context_invariant t \<sigma> \<gamma> \<theta> \<tau>` by metis
  have "\<tau>' = trans_post_raw sig (beval_raw t \<sigma> \<gamma> \<theta> e) (\<sigma> sig) (purge_raw \<tau> t dly sig (\<sigma> sig) (beval_raw t \<sigma> \<gamma> \<theta> e)) t dly"
    using \<tau>'_def unfolding inr_post_raw_def by auto
  hence "\<tau>'(t:=0) = (trans_post_raw sig (beval_raw t \<sigma> \<gamma> \<theta> e) (\<sigma> sig) ((purge_raw \<tau> t dly sig (\<sigma> sig) (beval_raw t \<sigma> \<gamma> \<theta> e))) t dly)(t:=0)"
    by auto
  also have "... = trans_post_raw sig (beval_raw t \<sigma> \<gamma> \<theta> e) (\<sigma> sig) ((purge_raw \<tau> t dly sig (\<sigma> sig) (beval_raw t \<sigma> \<gamma> \<theta> e))(t:=0)) t dly"
    using `0 < dly` post_necessary_raw_rem_curr_trans[OF `context_invariant t \<sigma> \<gamma> \<theta> (purge_raw \<tau> t dly sig (\<sigma> sig) (beval_raw t \<sigma> \<gamma> \<theta> e))`]
    by (metis (mono_tags, hide_lams) Bassign_inert.prems(1) Bassign_inert.prems(3) \<open>\<tau>' =
    trans_post_raw sig (beval_raw t \<sigma> \<gamma> \<theta> e) (\<sigma> sig) (purge_raw \<tau> t dly sig (\<sigma> sig) (beval_raw t \<sigma>
    \<gamma> \<theta> e)) t dly\<close> \<open>context_invariant t \<sigma> \<gamma> \<theta> (purge_raw \<tau> t dly sig (\<sigma> sig) (beval_raw t \<sigma> \<gamma> \<theta>
    e))\<close> context_invariant_def fun_upd_triv nonneg_delay.simps(5) nonneg_delay_same order_refl)
  also have "... = trans_post_raw sig (beval_raw t \<sigma> \<gamma> \<theta> e) (\<sigma> sig) (purge_raw (\<tau>(t:=0)) t dly sig (\<sigma> sig) (beval_raw t \<sigma> \<gamma> \<theta> e)) t dly"
    unfolding push_rem_curr_trans_purge_raw 
    by (metis (no_types, lifting) Bassign_inert.prems(3) context_invariant_def push_rem_curr_trans_purge_raw)
  also have "... = inr_post_raw sig (beval_raw t \<sigma> \<gamma> \<theta> e) (\<sigma> sig) (\<tau>(t:=0)) t dly"
    unfolding inr_post_raw_def by auto
  finally show ?case
    by (metis b_seq_exec.simps(5))
next
  case Bnull
  then show ?case by auto
qed

text \<open>The following lemma is based on the assumption (premise) that @{term "conc_stmt_wf cs"}. This
is because we want to employ the theorem @{thm "b_conc_exec_sequential"} where executing two parallel
processes can be seen as executing two sequential processes. This is, of course, relies on the
assumption that both processes do not modify the same signals.

A more fundamental question arises: can we prove this theorem without this well-formedness premise
and this theorem? We certainly would need to reason about @{term "clean_zip"} as this is the
primitive operation for handling parallel execution.\<close>

lemma b_conc_exec_mono_wrt_rem_curr_trans:
  assumes "t, \<sigma>, \<gamma>, \<theta> \<turnstile> <cs, \<tau>> \<longrightarrow>\<^sub>c \<tau>'"
  assumes "nonneg_delay_conc cs" and "conc_stmt_wf cs"
  assumes "context_invariant t \<sigma> \<gamma> \<theta> \<tau>"
  shows "t, \<sigma>, \<gamma>, \<theta> \<turnstile> <cs, \<tau>(t:=0)> \<longrightarrow>\<^sub>c (\<tau>'(t:=0))"
  using assms
proof (induction cs arbitrary: \<tau> \<tau>')
  case (Bpar cs1 cs2)
  define \<tau>1 where "\<tau>1 = b_conc_exec t \<sigma> \<gamma> \<theta> cs1 \<tau>"
  hence **: "t , \<sigma> , \<gamma> , \<theta> \<turnstile> <cs1 , \<tau>(t:=0)> \<longrightarrow>\<^sub>c \<tau>1(t:=0)"
    using Bpar unfolding conc_stmt_wf_def by fastforce
  have *: "\<tau>' = b_conc_exec t \<sigma> \<gamma> \<theta> cs2 \<tau>1"
    using b_conc_exec_sequential[OF `conc_stmt_wf (cs1 || cs2)`] Bpar(3) \<tau>1_def by auto
  with Bpar have "t , \<sigma> , \<gamma> , \<theta> \<turnstile> <cs2 , \<tau>1(t:=0)> \<longrightarrow>\<^sub>c \<tau>'(t:=0)"
    unfolding conc_stmt_wf_def
    by (metis \<tau>1_def b_conc_exec_preserves_context_invariant distinct_append
    nonneg_delay_conc.simps(2) signals_from.simps(2))
  then show ?case
    using * Bpar(3)  by (metis Bpar.prems(3) ** b_conc_exec_sequential)
next
  case (Bsingle sl ss)
  hence "nonneg_delay ss"
    by auto
  have "disjnt sl \<gamma> \<or> \<not> disjnt sl \<gamma>"
    by auto
  moreover
  { assume "disjnt sl \<gamma>"
    hence ?case
      using Bsingle.prems(1) by auto }
  moreover
  { assume "\<not> disjnt sl \<gamma>"
    hence "t, \<sigma>, \<gamma>, \<theta> \<turnstile> <ss, \<tau>> \<longrightarrow>\<^sub>s \<tau>'"
      using Bsingle by auto
    hence "t, \<sigma>, \<gamma>, \<theta> \<turnstile> <ss, \<tau>(t:=0)> \<longrightarrow>\<^sub>s \<tau>'(t:=0)"
      using b_seq_exec_mono_wrt_rem_curr_trans[OF _ `nonneg_delay ss`]  by (simp add: Bsingle.prems(4))
    hence ?case
      using `\<not> disjnt sl \<gamma>` by (metis b_conc_exec.simps(1)) }
  ultimately show ?case by auto
qed

lemma worldline_rem_curr_trans_eq:
  assumes "\<And>s. s \<in> dom (\<tau> t) \<Longrightarrow> \<sigma> s = the (\<tau> t s)"
  assumes "\<And>n. n < t \<Longrightarrow> \<tau> n = 0"
  shows "worldline2 t \<sigma> \<theta> \<tau> = worldline2 t \<sigma> \<theta> (\<tau>(t:=0))"
  using assms unfolding worldline2_def worldline_raw_def
  using signal_of_rem_curr_trans_at_t[where \<sigma>="\<sigma>" and \<tau>="\<tau>", OF assms] by auto 

lemma worldline2_constructible_rem_curr_trans:
  fixes tw :: "nat \<times> 'signal worldline"
  assumes "destruct_worldline tw = (t, \<sigma>, \<gamma>, \<theta>, \<tau>)"
  defines "\<tau>' \<equiv> \<tau>(t:=0)"
  shows "tw = worldline2 t \<sigma> \<theta> \<tau>' \<and> context_invariant t \<sigma> \<gamma> \<theta> \<tau>'"
proof -
  have "fst tw = t" and "tw = worldline2 t \<sigma> \<theta> \<tau> \<and> context_invariant t \<sigma> \<gamma> \<theta> \<tau>"
    using worldline2_constructible[OF assms(1)] by auto
  hence "\<And>n. n \<le> t \<Longrightarrow>  \<tau> n = 0"
    and " tw = worldline2 t \<sigma> \<theta> \<tau>"
    and " context_invariant t \<sigma> \<gamma> \<theta> \<tau>"
    unfolding context_invariant_def by auto
  hence "tw = worldline2 t \<sigma> \<theta> \<tau>'"
    unfolding \<tau>'_def by (metis fun_upd_triv order_refl)
  moreover have "context_invariant t \<sigma> \<gamma> \<theta> \<tau>'"
    unfolding \<tau>'_def using context_invariant_rem_curr_trans[OF `context_invariant t \<sigma> \<gamma> \<theta> \<tau>`]
    by auto
  ultimately show ?thesis
    by auto
qed

definition world_conc_exec2 :: "nat \<times> 'signal worldline \<Rightarrow> 'signal conc_stmt \<Rightarrow> nat \<times> 'signal worldline"
  where
  "world_conc_exec2 tw c = (let (t, \<sigma>, \<gamma>, \<theta>, \<tau>) = destruct_worldline tw;
                                             \<tau>' = b_conc_exec t \<sigma> \<gamma> \<theta> c (\<tau>(t:=0))
                             in worldline2 t \<sigma> \<theta> \<tau>')"

lemma world_conc_exec_rem_curr_trans_eq:
  assumes "nonneg_delay_conc c" and "conc_stmt_wf c"
  shows "world_conc_exec2 tw c = world_conc_exec tw c"
proof -
  let ?w = "snd tw"
  obtain t \<sigma> \<gamma> \<theta> \<tau> \<tau>' where des: "destruct_worldline tw = (t, \<sigma>, \<gamma>, \<theta>, \<tau>)" and  ex: "t, \<sigma>, \<gamma>, \<theta> \<turnstile> <c, \<tau>> \<longrightarrow>\<^sub>c \<tau>'"
    and ci: "context_invariant t \<sigma> \<gamma> \<theta> \<tau>"
    using destruct_worldline_exist worldline2_constructible by (metis)
  hence ex2: "t, \<sigma>, \<gamma>, \<theta> \<turnstile> <c, \<tau>(t:=0)> \<longrightarrow>\<^sub>c (\<tau>'(t:=0))"
    using b_conc_exec_mono_wrt_rem_curr_trans[OF _ assms] by auto
  moreover have "context_invariant t \<sigma> \<gamma> \<theta> \<tau>'"
    using b_conc_exec_preserves_context_invariant[OF ci ex assms(1)] by auto
  ultimately have "worldline2 t \<sigma> \<theta> \<tau>' = worldline2 t \<sigma> \<theta> (\<tau>'(t:=0))"
    using worldline_rem_curr_trans_eq unfolding context_invariant_def by (simp add: fun_upd_idem)
  thus ?thesis
    unfolding world_conc_exec2_def world_conc_exec_def Let_def using des ex ex2
    by auto
qed

subsection \<open>A sound and complete Hoare logic for VHDL's simulation\<close>

definition worldline_of_history :: "'signal trans_raw \<Rightarrow> 'signal worldline"
  where "worldline_of_history = signal_of False"

inductive world_sim_fin :: "nat \<times> 'signal worldline \<Rightarrow> nat \<Rightarrow> 'signal conc_stmt \<Rightarrow> nat \<times> 'signal worldline \<Rightarrow> bool"
  (" _, _, _ \<Rightarrow>\<^sub>S _") where
  "    destruct_worldline tw = (t, \<sigma>, \<gamma>, \<theta>, \<tau>)
   \<Longrightarrow> T, t, \<sigma>, \<gamma>, \<theta> \<turnstile> <cs, \<tau>> \<leadsto> res
   \<Longrightarrow> worldline_raw (get_time res) (get_state res) (get_beh res) (get_trans res) = w'
   \<Longrightarrow> tw, T, cs \<Rightarrow>\<^sub>S (get_time res, w')"

lemma
  assumes "T < fst tw"
  shows "tw, T, cs \<Rightarrow>\<^sub>S tw"
proof -
  obtain t \<sigma> \<gamma> \<theta> \<tau> where des: "destruct_worldline tw = (t, \<sigma>, \<gamma>, \<theta>, \<tau>)"
    by (meson destruct_worldline_def)
  hence "fst tw = t"
    unfolding destruct_worldline_def Let_def by auto
  with assms have "T < t" 
    by auto
  hence sim: "T, t, \<sigma>, \<gamma>, \<theta> \<turnstile> <cs, \<tau>> \<leadsto> (t, \<sigma>, \<theta>, \<tau>)"
    by (intro b_simulate_fin.intros(3)) auto
  define w' where "w' = worldline_raw (max (T + 1) t) \<sigma> \<theta> \<tau>"
  have "tw = worldline2 t \<sigma> \<theta> \<tau>" and " context_invariant t \<sigma> \<gamma> \<theta> \<tau>"
    using worldline2_constructible[OF des] by auto
  hence "snd tw = worldline_raw t \<sigma> \<theta> \<tau>"
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
    by (metis \<open>tw = worldline2 t \<sigma> \<theta> \<tau>\<close> comp_apply fst_conv snd_conv world_sim_fin.intros
    worldline2_def)
qed

inductive_cases world_sim_fin: "tw, T, cs \<Rightarrow>\<^sub>S tw'"

lemma premises_of_world_sim_fin:
  assumes "tw, T, cs \<Rightarrow>\<^sub>S tw'"
  shows "\<exists>t \<sigma> \<gamma> \<theta> \<tau> tres. destruct_worldline tw = (t, \<sigma>, \<gamma>, \<theta>, \<tau>) \<and> (T, t, \<sigma>, \<gamma>, \<theta> \<turnstile> <cs, \<tau>> \<leadsto> tres)
                          \<and> worldline_raw (get_time tres) (get_state tres) (get_beh tres) (get_trans tres) = snd tw' \<and> fst tw = t \<and> fst tw' = get_time tres"
  using world_sim_fin[OF assms] 
  by (smt comp_apply fst_conv fst_destruct_worldline snd_conv)

lemma premises_of_world_sim_fin':
  assumes "tw, T, cs \<Rightarrow>\<^sub>S tw'"
  obtains t \<sigma> \<gamma> \<theta> \<tau> tres where "destruct_worldline tw = (t, \<sigma>, \<gamma>, \<theta>, \<tau>)" and
    "T, t, \<sigma>, \<gamma>, \<theta> \<turnstile> <cs, \<tau>> \<leadsto> tres" and   "worldline_raw (get_time tres) (get_state tres) (get_beh tres) (get_trans tres) = snd tw'" 
    and "fst tw = t" and "fst tw' = get_time tres"
  using premises_of_world_sim_fin[OF assms] by auto

lemma world_maxtime_lt_fst_tres:
  assumes "tw, T, cs \<Rightarrow>\<^sub>S tw'"
  shows "T < fst tw'"
proof -
  obtain t \<sigma> \<gamma> \<theta> \<tau> tres where "destruct_worldline tw = (t, \<sigma>, \<gamma>, \<theta>, \<tau>)" and
                              "T, t, \<sigma>, \<gamma>, \<theta> \<turnstile> <cs, \<tau>> \<leadsto> tres" and   
                              "worldline_raw (get_time tres) (get_state tres) (get_beh tres) (get_trans tres) = snd tw'" 
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

definition world_quiet :: "nat \<times> 'signal worldline \<Rightarrow> bool" where
  "world_quiet tw \<longleftrightarrow> fst tw > worldline_deg (snd tw)"

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
  "\<forall>s. non_stuttering (to_trans_raw_sig (derivative_hist_raw w t)) def_state s"
proof
  fix s
  define ks where "ks = keys (to_trans_raw_sig (derivative_hist_raw w t) s)"
  { fix k1 k2 :: nat
    assume "k1 < k2" and "k1 \<in> ks" and "k2 \<in> ks"
    assume "\<forall>k. k1 < k \<and> k < k2 \<longrightarrow> k \<notin> ks"
    have "k1 < t"
      using `k1 \<in> ks` unfolding ks_def by (auto simp add: keys_at_most_t) 
    hence "to_trans_raw_sig (derivative_hist_raw w t) s k1 = Some (w s k1)"
      using `k1 \<in> ks` unfolding ks_def keys_def to_trans_raw_sig_def derivative_hist_raw_def
      difference_raw_def  using CollectD zero_option_def 
    proof -
      assume "k1 \<in> {k. (if t \<le> k then Map.empty else if k = 0 then \<lambda>s. if w s k then Some True else None else (\<lambda>s. if w s k \<noteq> w s (k - 1) then Some (w s k) else None)) s \<noteq> 0}"
      then have f1: "(if t \<le> k1 then Map.empty else if k1 = 0 then \<lambda>a. if w a k1 then Some True else None else (\<lambda>a. if w a k1 \<noteq> w a (k1 - 1) then Some (w a k1) else None)) s \<noteq> 0"
        by force
      then have f2: "\<not> t \<le> k1"
        using zero_option_def by fastforce
      then have "\<not> (if k1 = 0 then (if w s k1 then Some True else None) = 0 else (if w s k1 \<noteq> w s (k1 - 1) then Some (w s k1) else None) = 0)"
        using f1 by presburger
      then have f3: "k1 = 0 \<longrightarrow> w s 0"
        by (metis zero_option_def)
      have "\<not> (if k1 = 0 then (if w s k1 then Some True else None) = 0 else (if w s k1 \<noteq> w s (k1 - 1) then Some (w s k1) else None) = 0)"
        using f2 f1 by presburger
      moreover
      { assume "(if w s k1 \<noteq> w s (k1 - 1) then Some (w s k1) else None) = Some (w s k1)"
        then have "k1 = 0 \<or> (if t \<le> k1 then Map.empty else if k1 = 0 then \<lambda>a. if w a k1 then Some True else None else (\<lambda>a. if w a k1 \<noteq> w a (k1 - 1) then Some (w a k1) else None)) s = Some (w s k1)"
          using f2 by presburger }
      ultimately have "k1 = 0 \<or> (if t \<le> k1 then Map.empty else if k1 = 0 then \<lambda>a. if w a k1 then Some True else None else (\<lambda>a. if w a k1 \<noteq> w a (k1 - 1) then Some (w a k1) else None)) s = Some (w s k1)"
        by (metis zero_option_def)
      then show "(if t \<le> k1 then Map.empty else if k1 = 0 then \<lambda>a. if w a k1 then Some True else None else (\<lambda>a. if w a k1 \<noteq> w a (k1 - 1) then Some (w a k1) else None)) s = Some (w s k1)"
        using f3 f2 by presburger
    qed
    have "k2 < t"
      using `k2 \<in> ks` unfolding ks_def by (auto simp add: keys_at_most_t)
    hence "to_trans_raw_sig (derivative_hist_raw w t) s k2 = Some (w s k2)"
      using `k2 \<in> ks` `k1 < k2` unfolding ks_def keys_def to_trans_raw_sig_def derivative_hist_raw_def
      difference_raw_def  using CollectD zero_option_def by fastforce
    have "w s k1 \<noteq> w s k2"
    proof -
      have "\<forall>k. k1 < k \<and> k < k2 \<longrightarrow> w s k = w s k1"
      proof (rule, rule)
        fix k
        assume "k1 < k \<and> k < k2"
        hence "signal_of False (derivative_hist_raw w t) s k = w s k"
          using `k2 < t` by(intro signal_of_derivative_hist_raw)(auto)
        hence "w s k = signal_of False (derivative_hist_raw w t) s k"          
          by auto
        also have "... = signal_of False (derivative_hist_raw w t) s k1"
          using `\<forall>k. k1 < k \<and> k < k2 \<longrightarrow> k \<notin> ks` `k1 < k \<and> k < k2` unfolding ks_def
          by (intro signal_of_less_ind')(simp add: keys_def to_trans_raw_sig_def)+
        also have "... = w s k1"
          using `k1 < t` by(intro signal_of_derivative_hist_raw)(auto)
        finally show "w s k = w s k1"
          by auto
      qed
      hence "w s (k2 - 1) = w s k1"
        using `k1 < k2`
        by (metis Suc_diff_1 diff_less less_SucE less_Suc_eq_0_disj less_imp_Suc_add zero_less_one)
      moreover have "w s k2 \<noteq> w s (k2 - 1)"
        using `k2 \<in> ks`  `k1 < k2` `k2 < t` zero_option_def
        unfolding ks_def keys_def to_trans_raw_sig_def derivative_hist_raw_def difference_raw_def 
        by force
      ultimately show ?thesis
        by auto
    qed
    hence "to_trans_raw_sig (derivative_hist_raw w t) s k1 \<noteq>
           to_trans_raw_sig (derivative_hist_raw w t) s k2"
      using \<open>to_trans_raw_sig (derivative_hist_raw w t) s k2 = Some (w s k2)\<close>
      and \<open>to_trans_raw_sig (derivative_hist_raw w t) s k1 = Some (w s k1)\<close>
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
    hence "\<And>k. k < Least_key \<Longrightarrow> w s k = w s 0"
    proof -
      fix k
      assume "k < Least_key"
      hence "signal_of False (derivative_hist_raw w t) s k = w s k"
        using `Least_key < t` by (intro signal_of_derivative_hist_raw)(auto)
      hence "w s k = signal_of False (derivative_hist_raw w t) s k "
        by auto
      also have "... = signal_of False (derivative_hist_raw w t) s 0"
        using `k < Least_key` `\<And>k. k < Least_key \<Longrightarrow> k \<notin> ks` 
        by (intro signal_of_less_ind')(simp add: keys_def ks_def to_trans_raw_sig_def)+
      also have "... = w s 0"
        by (metis \<open>Least_key < t\<close> less_trans not_gr_zero signal_of_derivative_hist_raw)
      finally show "w s k = w s 0"
        by auto 
    qed
    have "Least_key = 0 \<or> 0 < Least_key"
      by auto
    moreover
    { assume "0 < Least_key"
      hence "w s Least_key \<noteq> w s (Least_key - 1)"
        using `Least_key \<in> ks` `Least_key < t` unfolding ks_def keys_def to_trans_raw_sig_def
        derivative_hist_raw_def difference_raw_def  using zero_option_def 
        by force
      hence "w s 0 \<noteq> w s Least_key"
        using \<open>0 < Least_key\<close> \<open>\<And>k. k < Least_key \<Longrightarrow> w s k = w s 0\<close> by fastforce
      moreover have "Some (w s Least_key) = to_trans_raw_sig (derivative_hist_raw w t) s Least_key"
        using `Least_key \<in> ks` `Least_key < t` unfolding ks_def keys_def to_trans_raw_sig_def
        derivative_hist_raw_def difference_raw_def using \<open>w s Least_key \<noteq> w s (Least_key - 1)\<close> 
        by (simp add: \<open>0 < Least_key\<close>)
      ultimately have "w s 0 \<noteq> the (to_trans_raw_sig (derivative_hist_raw w t) s (LEAST k. k \<in> ks))"
        unfolding Least_key_def  by (metis option.sel) 
      moreover have "w s 0 = False"
      proof (rule ccontr)
        assume "w s 0 \<noteq> False" hence "w s 0" by auto
        hence "0 \<in> ks"
          unfolding ks_def keys_def to_trans_raw_sig_def derivative_hist_raw_def difference_raw_def
          using `0 < Least_key` `Least_key < t` by (auto simp add: zero_option_def)
        thus False
          using \<open>0 < Least_key\<close> \<open>\<And>ka. ka < Least_key \<Longrightarrow> ka \<notin> ks\<close> by blast
      qed
      ultimately have "False \<noteq> the (to_trans_raw_sig (derivative_hist_raw w t) s (LEAST k. k \<in> ks))"
        by auto }
    moreover
    { assume "Least_key = 0"
      hence "0 \<in> ks"
        using `Least_key \<in> ks` by auto
      hence "derivative_hist_raw w t 0 s \<noteq> 0"
        unfolding ks_def keys_def to_trans_raw_sig_def by auto
      hence "derivative_hist_raw w t 0 s = Some True"
        using `Least_key < t` `Least_key = 0` unfolding derivative_hist_raw_def difference_raw_def
        by (smt zero_option_def)
      hence "False \<noteq> the (to_trans_raw_sig (derivative_hist_raw w t) s (LEAST k. k \<in> ks))"
        by (metis Least_key_def \<open>Least_key = 0\<close> option.sel to_trans_raw_sig_def) }
    ultimately have "False \<noteq> the (to_trans_raw_sig (derivative_hist_raw w t) s (LEAST k. k \<in> ks))"
      by auto }
  with first_po show "non_stuttering (to_trans_raw_sig (derivative_hist_raw w t)) def_state s"
    unfolding non_stuttering_def ks_def by auto
qed

definition next_time_world :: "nat \<times> 'signal worldline \<Rightarrow> nat" where
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
  assumes "\<tau> t sig = Some (\<not> def)"
  shows "signal_of def \<tau> sig t \<noteq> def"
proof -
  have "Femto_VHDL_raw.inf_time (to_trans_raw_sig \<tau>) sig t = Some t"
  proof (rule inf_time_someI)
    show "t \<in> dom ((to_trans_raw_sig \<tau> sig))"
      using assms(1) by (auto simp add: to_trans_raw_sig_def)
  qed auto
  hence "signal_of def \<tau> sig t = the ((to_trans_raw_sig \<tau> sig) t)"
    unfolding Femto_VHDL_raw.to_signal_def comp_def by auto
  also have "... \<longleftrightarrow> \<not> def"
    using assms(1) by (auto simp add: to_trans_raw_sig_def)
  finally show ?thesis
    by auto
qed

lemma signal_of_defaultE:
  assumes "signal_of def \<tau> sig t = def"
  shows "\<tau> t sig = None \<or> \<tau> t sig = Some def"
  using assms
proof (rule contrapos_pp)
  assume " \<not> (\<tau> t sig = None \<or> \<tau> t sig = Some def) "
  hence "\<tau> t sig = Some (\<not> def)"
    by auto
  thus "signal_of def \<tau> sig t \<noteq> def"
    by (meson signal_of_not_default)
qed

lemma next_time_world_alt_def1:
  assumes "derivative_raw (snd tw) (fst tw) \<noteq> 0"
  shows "next_time_world tw = (LEAST n. n \<ge> fst tw \<and> (\<lambda>s. snd tw s (fst tw)) \<noteq> (\<lambda>s. snd tw s n))"
proof -
  define t where "t = fst tw"
  define w where "w = snd tw"
  define \<tau> where "\<tau> = derivative_raw w t"
  have non_stut: "\<forall>s. non_stuttering (to_trans_raw_sig \<tau>) (\<lambda>s. w s t) s"
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
  hence non_stut_sig: "non_stuttering (to_trans_raw_sig \<tau>) (\<lambda>s. w s t) sig"
    using non_stut by auto
  have "(\<lambda>s. w s t) \<noteq> (\<lambda>s. w s (next_time_world tw))"
  proof
    let ?\<sigma> = "\<lambda>s. w s t"
    assume " (\<lambda>s. w s t) = (\<lambda>s. w s (next_time_world tw))"
    hence "w sig t = w sig (next_time_world tw)"
      by metis
    moreover have helper1: "w sig t = signal_of (?\<sigma> sig) \<tau> sig t"
      by (metis (full_types) \<tau>_def derivative_hist_raw_ensure_non_stuttering signal_of_derivative_raw_t)
    moreover have " signal_of (?\<sigma> sig)  \<tau> sig ?t' = w sig ?t'"
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
      using \<open>signal_of (w sig t) \<tau> sig t = signal_of (w sig t) \<tau> sig (next_time_world tw)\<close>
      by blast
    hence "\<tau> ?t' sig = None"
      using \<open>t < next_time_world tw\<close> current_sig_and_prev_same non_stut_sig zero_option_def
      by fastforce
    with `\<tau> ?t' sig = Some val` show False by auto
  qed
  have "(LEAST n. n \<ge> t \<and> (\<lambda>s. w s t) \<noteq> (\<lambda>s. w s n)) = next_time_world tw"
  proof (rule Least_equality)
    show "t \<le> next_time_world tw \<and> (\<lambda>s. w s t) \<noteq> (\<lambda>s. w s (next_time_world tw))"
      by (simp add: \<open>(\<lambda>s.  w s t) \<noteq> (\<lambda>s.  w s (next_time_world tw))\<close> \<open>t \<le> next_time_world tw\<close>)
  next
    { fix y
      let ?\<sigma> = "\<lambda>s.  w s t"
      assume "\<not> ?t' \<le> y" hence "y < ?t'" by auto
      have "y < t \<or> \<not> y < t" by auto
      moreover
      { assume "\<not> y < t" hence "t \<le> y" by auto
        have "\<And>n. t < n \<Longrightarrow> n \<le> y \<Longrightarrow> \<tau> n = 0"
          using `y < ?t'` t'_def
          by (metis \<open>next_time_world tw = Femto_VHDL_raw.next_time t \<tau>\<close> le_less_trans  next_time_at_least2)
        have "\<And>s.  w s t = signal_of (?\<sigma> s) \<tau> s t"
          using `\<And>n. n \<le> t \<Longrightarrow> \<tau> n = 0`
          by (metis signal_of_less_ind signal_of_zero zero_fun_def zero_le)
        moreover have "\<And>s. signal_of (?\<sigma> s) \<tau> s y =  w s y"
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
        ultimately have "(\<lambda>s.  w s t) = (\<lambda>s.  w s y)"
          by blast
        hence "\<not> (t \<le> y \<and> (\<lambda>s.  w s t) \<noteq> (\<lambda>s.  w s y))"
          by auto }
      moreover
      { assume "y < t"
        hence "\<not> (t \<le> y \<and> (\<lambda>s.  w s t) \<noteq> (\<lambda>s.  w s y))"
          by auto }
      ultimately have "\<not> (t \<le> y \<and> (\<lambda>s.  w s t) \<noteq> (\<lambda>s.  w s y))"
        by auto }
    thus "\<And>y. t \<le> y \<and> (\<lambda>s.  w s t) \<noteq> (\<lambda>s.  w s y) \<Longrightarrow> ?t' \<le> y"
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
  "derivative_raw (snd tw) (fst tw) \<noteq> 0 \<longleftrightarrow>  (\<exists>n\<ge> (fst tw). (\<lambda>s. (snd tw) s (fst tw)) \<noteq> (\<lambda>s. (snd tw) s n))"
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
  hence "snd tw s least \<noteq> snd tw s (least - 1)" 
    using `fst tw < least` unfolding difference_raw_def by force
  have **: "\<forall>n<least. derivative_raw (snd tw) (fst tw) n = Map.empty"
    unfolding least_def using not_less_Least by blast
  have "\<forall>n. fst tw < n \<and> n < least \<longrightarrow> snd tw s n = snd tw s (fst tw)"
  proof (intro allI, intro impI)
    fix n
    assume "fst tw < n \<and> n < least"
    hence "derivative_raw (snd tw) (fst tw) n = Map.empty" and "fst tw < n" and "n < least"
      using ** by auto
    have "signal_of (snd tw s (fst tw)) (derivative_raw (snd tw) (fst tw)) s n = (snd tw) s n"
      by (intro signal_of_derivative_raw[OF order.strict_implies_order[OF `fst tw < n`]])(simp)
    hence "(snd tw) s n = signal_of (snd tw s (fst tw)) (derivative_raw (snd tw) (fst tw)) s n"
      by auto
    also have "... = signal_of (snd tw s (fst tw)) (derivative_raw (snd tw) (fst tw)) s (fst tw)"
      by(intro signal_of_less_ind')        
        (simp add: \<open>fst tw < n \<and> n < least\<close> ** le_less_trans zero_option_def order.strict_implies_order)+
    also have "... = (snd tw) s (fst tw)"
      by (intro signal_of_derivative_raw_t)(simp)
    finally show "snd tw s n = snd tw s (fst tw)"
      by auto
  qed
  hence "snd tw s (least - 1) = snd tw s (fst tw)"
    using `fst tw < least` 
    by (metis (no_types, lifting) Suc_diff_1 diff_less less_SucE less_Suc_eq_0_disj
    less_imp_Suc_add zero_less_one)
  hence "snd tw s least \<noteq> snd tw s (fst tw)"
    using `snd tw s least \<noteq> snd tw s (least - 1)` by auto
  with `fst tw < least` show "\<exists>n\<ge>fst tw. (\<lambda>s. snd tw s (fst tw)) \<noteq> (\<lambda>s. snd tw s n)"
    by(intro exI[where x="least"])(meson order.strict_implies_order)
next
  assume *: "\<exists>n\<ge>fst tw. (\<lambda>s. snd tw s (fst tw)) \<noteq> (\<lambda>s. snd tw s n)"
  define least where "least = (LEAST n. n \<ge> fst tw \<and> (\<lambda>s. snd tw s (fst tw)) \<noteq> (\<lambda>s. snd tw s n))"
  hence "fst tw \<le> least" and **: "(\<lambda>s. snd tw s (fst tw)) \<noteq> (\<lambda>s. snd tw s least)"
    using LeastI_ex[OF *] unfolding least_def by auto
  hence "fst tw < least"
    using nat_less_le by blast
  have "\<forall>n. fst tw < n \<and> n < least \<longrightarrow> (\<forall>s. snd tw s (fst tw) = snd tw s n)"
    unfolding least_def  by (metis (mono_tags, lifting) Least_le leD le_eq_less_or_eq)
  hence "(\<lambda>s. snd tw s (fst tw)) = (\<lambda>s. snd tw s (least - 1))"
    using `fst tw < least` 
    by (intro ext) 
       (metis Suc_diff_1 diff_less le_neq_implies_less le_simps(2) less_Suc_eq_0_disj
       less_imp_Suc_add zero_less_one)
  hence "(\<lambda>s. snd tw s least) \<noteq> (\<lambda>s. snd tw s (least - 1))"
    using ** by auto
  have "difference_raw (snd tw) least \<noteq> 0"
  proof (rule ccontr)
    assume "\<not> difference_raw (snd tw) least \<noteq> 0" hence "difference_raw (snd tw) least = 0"
      by auto
    hence "(\<lambda>s. if snd tw s least \<noteq> snd tw s (least - 1) then Some (snd tw s least) else None) = 0"
      using `fst tw < least` unfolding difference_raw_def by auto
    hence "(\<lambda>s. snd tw s least) = (\<lambda>s. snd tw s (least - 1))"
      by (intro ext)(smt option.distinct(1) zero_fun_def zero_option_def)
    with `(\<lambda>s. snd tw s least) \<noteq> (\<lambda>s. snd tw s (least - 1))` show False
      by auto
  qed
  hence "derivative_raw (snd tw) (fst tw) least \<noteq> 0"
    using `fst tw < least` unfolding derivative_raw_def by auto
  thus "derivative_raw (snd tw) (fst tw) \<noteq> 0"
    by (metis zero_fun_def)
qed

lemma next_time_world_alt_def: 
  "next_time_world tw = (let t =fst tw; w = snd tw in 
                            if \<exists>n\<ge>t. (\<lambda>s. w s t) \<noteq> (\<lambda>s. w s n) then (LEAST n. n \<ge> t \<and> (\<lambda>s. w s t) \<noteq> (\<lambda>s. w s n))
                            else t + 1)"
proof -
  have "derivative_raw (snd tw) (fst tw) = 0 \<or> derivative_raw (snd tw) (fst tw) \<noteq> 0"
    by auto
  moreover
  { assume "derivative_raw (snd tw) (fst tw) \<noteq> 0"
    hence "(\<exists>n\<ge> (fst tw). (\<lambda>s. (snd tw) s (fst tw)) \<noteq> (\<lambda>s. (snd tw) s n))"
      unfolding derivative_raw_alt_def by auto
    hence ?thesis
      using next_time_world_alt_def1[OF `derivative_raw (snd tw) (fst tw) \<noteq> 0`]
      unfolding Let_def by auto }
  moreover
  { assume "derivative_raw (snd tw) (fst tw) = 0"
    hence "\<not> (\<exists>n\<ge> (fst tw). (\<lambda>s. (snd tw) s (fst tw)) \<noteq> (\<lambda>s. (snd tw) s n))"
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
  have "\<exists>n\<ge>get_time tw. (\<lambda>s. snd tw s (get_time tw)) \<noteq> (\<lambda>s. snd tw s n) \<or> 
       \<not> (\<exists>n\<ge>get_time tw. (\<lambda>s. snd tw s (get_time tw)) \<noteq> (\<lambda>s. snd tw s n))"
    by auto
  moreover
  { assume "\<not> (\<exists>n\<ge>get_time tw. (\<lambda>s. snd tw s (get_time tw)) \<noteq> (\<lambda>s. snd tw s n))"
    hence "next_time_world tw = get_time tw + 1"
      unfolding next_time_world_alt_def Let_def by auto
    hence "fst tw < next_time_world tw"
      by auto }
  moreover
  { assume *: "\<exists>n\<ge>get_time tw. (\<lambda>s. snd tw s (get_time tw)) \<noteq> (\<lambda>s. snd tw s n)"
    hence "next_time_world tw = (LEAST n. get_time tw \<le> n \<and> (\<lambda>s. snd tw s (get_time tw)) \<noteq> (\<lambda>s. snd tw s n))"
      unfolding next_time_world_alt_def Let_def by auto
    hence "get_time tw < next_time_world tw"
      using LeastI_ex[OF *] by auto
    hence "fst tw < next_time_world tw"
      by auto }
  ultimately show ?thesis by auto
qed

lemma unchanged_until_next_time_world:
  "\<forall>i\<ge>fst tw. i < next_time_world tw \<longrightarrow> (\<forall>s. snd tw s i = snd tw s (fst tw))"
proof (rule allI, rule impI, rule impI)
  fix i 
  assume "fst tw \<le> i"
  assume "i < next_time_world tw"
  have "   \<exists>n\<ge>get_time tw. (\<lambda>s. snd tw s (get_time tw)) \<noteq> (\<lambda>s. snd tw s n) \<or> 
        \<not> (\<exists>n\<ge>get_time tw. (\<lambda>s. snd tw s (get_time tw)) \<noteq> (\<lambda>s. snd tw s n))"
    by auto
  moreover
  { assume "\<exists>n\<ge>get_time tw. (\<lambda>s. snd tw s (get_time tw)) \<noteq> (\<lambda>s. snd tw s n)"
    hence "next_time_world tw = (LEAST n. get_time tw \<le> n \<and> (\<lambda>s. snd tw s (get_time tw)) \<noteq> (\<lambda>s. snd tw s n))"
      unfolding next_time_world_alt_def Let_def by auto
    hence "i < (LEAST n. fst tw  \<le> n \<and> (\<lambda>s. snd tw s (get_time tw)) \<noteq> (\<lambda>s. snd tw s n))"
      using \<open>i < next_time_world tw\<close> by auto
    hence "\<not> (get_time tw \<le> i \<and> (\<lambda>s. snd tw s (get_time tw)) \<noteq> (\<lambda>s. snd tw s i))"
      using not_less_Least by auto
    with \<open>fst tw \<le> i\<close> have "\<forall>s. snd tw s i = snd tw s (fst tw)"
      by meson }
  moreover 
  { assume "\<not> (\<exists>n\<ge>get_time tw. (\<lambda>s. snd tw s (get_time tw)) \<noteq> (\<lambda>s. snd tw s n))"
    hence "\<forall>n\<ge>fst tw. \<forall>s. snd tw s n = snd tw s (fst tw)"
      by meson
    hence "\<forall>s. snd tw s i = snd tw s (fst tw)"
      using \<open>fst tw \<le> i\<close>  by blast }
  ultimately show "\<forall>s. snd tw s i = snd tw s (fst tw)"
    by auto
qed

lemma successive_empty_event:
  assumes "event_of tw = {}" and "event_of (next_time_world tw, snd tw) = {}"
  shows "next_time_world tw = fst tw + 1"
proof (rule ccontr)
  assume "next_time_world tw \<noteq> fst tw + 1"
  hence "fst tw + 1 < next_time_world tw"
    using next_time_world_at_least by (metis discrete less_le)
  hence *: "\<exists>n\<ge>fst tw. (\<lambda>s. snd tw s (fst tw)) \<noteq> (\<lambda>s. snd tw s n)" and 
        "next_time_world tw = (LEAST n. get_time tw \<le> n \<and> (\<lambda>s. snd tw s (get_time tw)) \<noteq> (\<lambda>s. snd tw s n))"
    unfolding next_time_world_alt_def Let_def  by presburger+
  hence "(\<lambda>s. snd tw s (get_time tw)) \<noteq> (\<lambda>s. snd tw s (next_time_world tw))"
    using LeastI_ex[OF *]  by simp
  hence **: "\<exists>s. snd tw s (next_time_world tw) \<noteq> snd tw s (fst tw)"
    by auto
  have "\<And>s. snd tw s (next_time_world tw) = snd tw s (next_time_world tw - 1)"
    using assms(2) unfolding event_of_alt_def 
    by (smt diff_0_eq_0 empty_Collect_eq fst_conv snd_conv)
  thus False
    by (metis ** \<open>get_time tw + 1 < next_time_world tw\<close> diff_Suc_1 le_less lessI less_diff_conv 
        less_imp_Suc_add unchanged_until_next_time_world)
qed

inductive
  conc_sim :: "'signal assn2 \<Rightarrow> 'signal conc_stmt \<Rightarrow> 'signal assn2 \<Rightarrow> bool"
  ("\<turnstile>\<^sub>s (\<lbrace>(1_)\<rbrace>/ (_)/ \<lbrace>(1_)\<rbrace>)" 50)
  where
While: "\<turnstile> \<lbrace>\<lambda>tw. P tw\<rbrace> cs \<lbrace> \<lambda>tw. P (next_time_world tw, snd tw)\<rbrace>  \<Longrightarrow> \<turnstile>\<^sub>s \<lbrace>P\<rbrace> cs \<lbrace>P\<rbrace>" |
Conseq_sim: "\<forall>tw. P' tw \<longrightarrow> P tw \<Longrightarrow> \<turnstile>\<^sub>s \<lbrace>P\<rbrace> cs \<lbrace>Q\<rbrace> \<Longrightarrow> \<forall>tw. Q tw \<longrightarrow> Q' tw \<Longrightarrow> \<turnstile>\<^sub>s \<lbrace>P'\<rbrace> cs \<lbrace>Q'\<rbrace>"

lemma worldline_next_config:
  assumes "context_invariant t \<sigma> \<gamma> \<theta> \<tau>'"
  shows "worldline_raw t \<sigma> \<theta> \<tau>' = worldline_raw (next_time t \<tau>') (next_state t \<tau>' \<sigma>) (add_to_beh \<sigma> \<theta> t (next_time t \<tau>')) \<tau>'"
proof (rule ext)+
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
    hence "signal_of False \<theta> s' t' = signal_of False (add_to_beh \<sigma> \<theta> t (next_time t \<tau>')) s' t'"
      by (metis eq_imp_le signal_of_equal_when_trans_equal_upto)
    hence "worldline_raw t \<sigma> \<theta> \<tau>' s' t' = worldline_raw (next_time t \<tau>') (next_state t \<tau>' \<sigma>) (add_to_beh \<sigma> \<theta> t (next_time t \<tau>')) \<tau>' s' t'"
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
    hence "worldline_raw t \<sigma> \<theta> \<tau>' s' t' =
         worldline_raw (next_time t \<tau>') (next_state t \<tau>' \<sigma>) (add_to_beh \<sigma> \<theta> t (next_time t \<tau>')) \<tau>' s' t'"
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
    moreover have "signal_of False (\<theta>(t :=Some o \<sigma>)) s' t' = \<sigma> s'"
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
    ultimately have "signal_of (\<sigma> s') \<tau>' s' t' = signal_of False (\<theta>(t :=Some o \<sigma>)) s' t'"
      by auto
    hence "signal_of (\<sigma> s') \<tau>' s' t' = signal_of False (add_to_beh \<sigma> \<theta> t (next_time t \<tau>')) s' t'"
      unfolding add_to_beh by auto
    hence "worldline_raw t \<sigma> \<theta> \<tau>' s' t' = worldline_raw (next_time t \<tau>') (next_state t \<tau>' \<sigma>) (add_to_beh \<sigma> \<theta> t (next_time t \<tau>')) \<tau>' s' t'"
      unfolding worldline_raw_def using `t \<le> t' \<and> t' < next_time t \<tau>'` by auto }
  ultimately show "worldline_raw t \<sigma> \<theta> \<tau>' s' t' = worldline_raw (next_time t \<tau>') (next_state t \<tau>' \<sigma>) (add_to_beh \<sigma> \<theta> t (next_time t \<tau>')) \<tau>' s' t'"
    by auto
qed

lemma worldline_next_config_next_time:
  assumes "context_invariant t \<sigma> \<gamma> \<theta> \<tau>'"
  shows "worldline_raw t \<sigma> \<theta> \<tau>' = worldline_raw (next_time t \<tau>') (next_state t \<tau>' \<sigma>) (add_to_beh \<sigma> \<theta> t (next_time t \<tau>')) (\<tau>'(next_time t \<tau>' := 0))"
proof (rule ext)+
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
    hence "signal_of False \<theta> s' t' = signal_of False (add_to_beh \<sigma> \<theta> t (next_time t \<tau>')) s' t'"
      by (metis order_refl signal_of_equal_when_trans_equal_upto)
    hence "worldline_raw t \<sigma> \<theta> \<tau>' s' t' = worldline_raw (next_time t \<tau>') (next_state t \<tau>' \<sigma>) (add_to_beh \<sigma> \<theta> t (next_time t \<tau>')) (\<tau>'(next_time t \<tau>' := 0)) s' t'"
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
    hence "worldline_raw t \<sigma> \<theta> \<tau>' s' t' =
         worldline_raw (next_time t \<tau>') (next_state t \<tau>' \<sigma>) (add_to_beh \<sigma> \<theta> t (next_time t \<tau>')) (\<tau>'(next_time t \<tau>' := 0)) s' t'"
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
    moreover have "signal_of False (\<theta>(t := Some o \<sigma>)) s' t' = \<sigma> s'"
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
    ultimately have "signal_of (\<sigma> s') \<tau>' s' t' = signal_of False (\<theta>(t := Some o \<sigma>)) s' t'"
      by auto
    hence "signal_of (\<sigma> s') \<tau>' s' t' = signal_of False (add_to_beh \<sigma> \<theta> t (next_time t \<tau>')) s' t'"
      unfolding add_to_beh by auto
    hence "worldline_raw t \<sigma> \<theta> \<tau>' s' t' = worldline_raw (next_time t \<tau>') (next_state t \<tau>' \<sigma>) (add_to_beh \<sigma> \<theta> t (next_time t \<tau>')) (\<tau>'(next_time t \<tau>' := 0)) s' t'"
      unfolding worldline_raw_def using `t \<le> t' \<and> t' < next_time t \<tau>'` by auto }
  ultimately show "worldline_raw t \<sigma> \<theta> \<tau>' s' t' = worldline_raw (next_time t \<tau>') (next_state t \<tau>' \<sigma>) (add_to_beh \<sigma> \<theta> t (next_time t \<tau>')) (\<tau>'(next_time t \<tau>' := 0)) s' t'"
    by auto
qed

lemma worldline2_next_config:
  assumes "context_invariant t \<sigma> \<gamma> \<theta> \<tau>'"
  shows "(next_time t \<tau>', snd (worldline2 t \<sigma> \<theta> \<tau>')) = worldline2 (next_time t \<tau>') (next_state t \<tau>' \<sigma>) (add_to_beh \<sigma> \<theta> t (next_time t \<tau>')) \<tau>'"
proof -
  have "worldline_raw t \<sigma> \<theta> \<tau>' = worldline_raw (next_time t \<tau>') (next_state t \<tau>' \<sigma>) (add_to_beh \<sigma> \<theta> t (next_time t \<tau>')) \<tau>'"
    using worldline_next_config assms by metis
  thus ?thesis
    unfolding worldline2_def by auto
qed

lemma worldline2_next_config_next_time:
  assumes "context_invariant t \<sigma> \<gamma> \<theta> \<tau>'"
  shows "(next_time t \<tau>', snd (worldline2 t \<sigma> \<theta> \<tau>')) = worldline2 (next_time t \<tau>') (next_state t \<tau>' \<sigma>) (add_to_beh \<sigma> \<theta> t (next_time t \<tau>')) (\<tau>'(next_time t \<tau>' := 0))"
proof -
  have "worldline_raw t \<sigma> \<theta> \<tau>' = worldline_raw (next_time t \<tau>') (next_state t \<tau>' \<sigma>) (add_to_beh \<sigma> \<theta> t (next_time t \<tau>')) (\<tau>'(next_time t \<tau>' := 0))"
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

lemma while_soundness2:
  assumes "\<Turnstile> \<lbrace>\<lambda>tw. P tw \<rbrace> cs \<lbrace>\<lambda>tw. P (next_time_world tw, snd tw)\<rbrace>"
  assumes "tw, T, cs \<Rightarrow>\<^sub>S tw'"
  assumes "P tw"
  assumes "nonneg_delay_conc cs" and "conc_stmt_wf cs"
  shows   "P tw'"
proof -
  obtain t \<sigma> \<gamma> \<theta> \<tau> res where des: "destruct_worldline tw = (t, \<sigma>, \<gamma>, \<theta>, \<tau>)" and
  sim: "T, t, \<sigma>, \<gamma>, \<theta> \<turnstile> <cs, \<tau>> \<leadsto> res" and   woh: "tw' = (get_time res, worldline_raw (get_time res) (get_state res) (get_beh res) (get_trans res))"
    using premises_of_world_sim_fin'[OF assms(2)] 
    by (smt prod.exhaust_sel)
  have tau_def:  "\<tau> = derivative_raw (snd tw) (fst tw)" and
      sigma_def: "\<sigma> = (\<lambda>s. snd tw s (fst tw))" and
      theta_def: "\<theta> = derivative_hist_raw (snd tw) (fst tw)" and
      gamma_def: "\<gamma> = {s. snd tw s (fst tw) \<noteq> signal_of False (derivative_hist_raw (snd tw) (fst tw)) s (fst tw - 1)}"
    using des unfolding destruct_worldline_def Let_def by auto
  have non_stut: "\<forall>s. non_stuttering (to_trans_raw_sig \<tau>) \<sigma> s"
    using derivative_raw_ensure_non_stuttering unfolding tau_def sigma_def by metis
  have non_stut2: "\<forall>s. non_stuttering (to_trans_raw_sig \<theta>) def_state s"
    using derivative_hist_raw_ensure_non_stuttering unfolding sigma_def theta_def by metis
  have "tw = worldline2 t \<sigma> \<theta> \<tau>" and "context_invariant t \<sigma> \<gamma> \<theta> \<tau>"
    using worldline2_constructible[OF des] by auto
  with sim show ?thesis
    using woh assms(1) assms(3-5) non_stut gamma_def
  proof (induction arbitrary: tw rule:b_simulate_fin.induct)
    case (1 t maxtime \<tau> \<gamma> \<sigma> \<theta> cs \<tau>' res)
    hence "\<And>n. n \<le> t \<Longrightarrow> \<tau> n = 0"
      unfolding context_invariant_def by auto
    have "snd tw = worldline_raw t \<sigma> \<theta> \<tau>"
      using 1(5-6) unfolding worldline2_def by auto
    obtain tw_conc where "tw, cs \<Rightarrow>\<^sub>c tw_conc" by auto
    with `P tw`  have "P (next_time_world tw_conc, snd tw_conc)"
      using 1(9) unfolding conc_hoare_valid_def by blast
    have "fst tw = fst tw_conc"
      using fst_world_conc_exec `tw, cs \<Rightarrow>\<^sub>c tw_conc` by metis
    have "world_conc_exec tw cs = tw_conc"
      using world_conc_exec_rem_curr_trans_eq[OF 1(11-12)] `tw, cs \<Rightarrow>\<^sub>c tw_conc` by auto
    have " \<tau> t = 0"
      by (auto simp add: `\<And>n. n \<le> t \<Longrightarrow> \<tau> n = 0`)
    hence "t < next_time t \<tau>'"
      using  nonneg_delay_conc_next_time_strict[OF _ `t , \<sigma> , \<gamma> , \<theta> \<turnstile> <cs , \<tau>> \<longrightarrow>\<^sub>c \<tau>'` `nonneg_delay_conc cs` `conc_stmt_wf cs`]
      \<open>\<And>n. n \<le> t \<Longrightarrow> \<tau> n = 0\<close> dual_order.order_iff_strict by auto
    have ci: "context_invariant (next_time t \<tau>') (next_state t \<tau>' \<sigma>) (next_event t \<tau>' \<sigma>) (add_to_beh \<sigma> \<theta> t (next_time t \<tau>')) (\<tau>'(next_time t \<tau>' := 0))"
      using context_invariant[OF 1(7) 1(3) `t < next_time t \<tau>'`]  by auto
    obtain time sigma gamma theta tau where dw_def: "destruct_worldline tw = (time, sigma, gamma, theta, tau)"
      using destruct_worldline_exist by blast
    hence  "time = t" and "sigma = \<sigma>" and "gamma = \<gamma>" and
           same_beh: "\<And>k s. signal_of False \<theta> s k = signal_of False theta s k"  and
           same_trans: "\<And>k s. signal_of (\<sigma> s) \<tau> s k = signal_of (\<sigma> s) tau s k"
      using destruct_worldline_correctness[OF `context_invariant t \<sigma> \<gamma> \<theta> \<tau>`]
      unfolding `tw = worldline2 t \<sigma> \<theta> \<tau>` by auto
    moreover have "tau = \<tau>"
      using dw_def unfolding destruct_worldline_def Let_def `tw = worldline2 t \<sigma> \<theta> \<tau>`
      using derivative_raw_of_worldline2 `context_invariant t \<sigma> \<gamma> \<theta> \<tau>` 1(13) 
      unfolding context_invariant_def by auto
    ultimately have "destruct_worldline tw = (t, \<sigma>, \<gamma>, theta, \<tau>)"
      using dw_def by auto
    hence "context_invariant t \<sigma> \<gamma> theta \<tau>"
      using worldline2_constructible by blast
    obtain tau' where "t, \<sigma>, \<gamma>, theta \<turnstile> <cs, \<tau>> \<longrightarrow>\<^sub>c tau'"
      by auto
    hence "\<And>s' t'. signal_of (\<sigma> s') \<tau>' s' t' = signal_of (\<sigma> s') tau' s' t'"
      using helper_b_conc[OF 1(3) same_beh _ `t, \<sigma>, \<gamma>, theta \<turnstile> <cs, \<tau>> \<longrightarrow>\<^sub>c tau'`] 
      `context_invariant t \<sigma> \<gamma> theta \<tau>` `context_invariant t \<sigma> \<gamma> \<theta> \<tau>`
      `nonneg_delay_conc cs` `\<forall>a. non_stuttering (to_trans_raw_sig \<tau>) \<sigma> a`
      unfolding context_invariant_def  
      by auto
    hence "worldline_raw t \<sigma> \<theta> \<tau>' = worldline_raw t \<sigma> theta tau'"
      unfolding worldline_raw_def using same_beh by auto
    hence "worldline2 t \<sigma> \<theta> \<tau>' = worldline2 t \<sigma> theta tau'"
      unfolding worldline2_def by auto
    also have "... = tw_conc"
      using `world_conc_exec tw cs = tw_conc` unfolding world_conc_exec_def Let_def
      using `destruct_worldline tw = (t, \<sigma>, \<gamma> , theta, \<tau>)`
      by (simp add: \<open>t , \<sigma> , \<gamma> , theta \<turnstile> <cs , \<tau>> \<longrightarrow>\<^sub>c tau'\<close>)
    finally have "worldline2 t \<sigma> \<theta> \<tau>' = tw_conc"
      by auto
    hence "fst tw_conc = t"
      by auto
    have "snd tw_conc = worldline_raw t \<sigma> \<theta> \<tau>'"
      using `worldline2 t \<sigma> \<theta> \<tau>' = tw_conc` unfolding worldline2_def by auto
    have "context_invariant t \<sigma> \<gamma> \<theta> \<tau>'"
      using b_conc_exec_preserves_context_invariant[OF `context_invariant t \<sigma> \<gamma> \<theta> \<tau>` 1(3) `nonneg_delay_conc cs`]
      by auto
    hence "\<And>n. n \<le> t \<Longrightarrow> \<tau>' n = 0"
      unfolding context_invariant_def by auto
    have "\<forall>s. non_stuttering (to_trans_raw_sig \<tau>') \<sigma> s"
      using b_conc_exec_preserves_non_stuttering[OF `t , \<sigma> , \<gamma> , \<theta> \<turnstile> <cs , \<tau>> \<longrightarrow>\<^sub>c \<tau>'`]
      rem_curr_trans_preserve_trans_removal[OF `\<And>n. n \<le> t \<Longrightarrow> \<tau> n = 0`]
      `nonneg_delay_conc cs` `context_invariant t \<sigma> \<gamma> \<theta> \<tau>` `\<forall>s. non_stuttering (to_trans_raw_sig \<tau>) \<sigma> s`
      `conc_stmt_wf cs` \<open>\<And>n. n \<le> t \<Longrightarrow> \<tau> n = 0\<close>  by blast
    have "next_time_world tw_conc = next_time t \<tau>'"
      unfolding next_time_world_def Let_def `snd tw_conc = worldline_raw t \<sigma> \<theta> \<tau>'`
      using derivative_raw_of_worldline `context_invariant t \<sigma> \<gamma> \<theta> \<tau>'` `\<forall>s. non_stuttering (to_trans_raw_sig \<tau>') \<sigma> s`
      unfolding world_quiet_def worldline_deg_def `fst tw = fst tw_conc` `snd tw_conc = worldline_raw t \<sigma> \<theta> \<tau>'`
      context_invariant_def 
      by (simp add: derivative_raw_of_worldline_specific \<open>fst tw_conc = t\<close>)
    hence twc: "(next_time_world tw_conc, snd tw_conc) =
             worldline2 (next_time t \<tau>') (next_state t \<tau>' \<sigma>) (add_to_beh \<sigma> \<theta> t (next_time t \<tau>')) (\<tau>'(next_time t \<tau>' := 0))"
      using `worldline2 t \<sigma> \<theta> \<tau>' = tw_conc` worldline2_next_config_next_time[OF `context_invariant t \<sigma> \<gamma> \<theta> \<tau>'`]
      by auto
    have ns: " \<forall>s. non_stuttering (to_trans_raw_sig (\<tau>'(next_time t \<tau>' := 0))) (next_state t \<tau>' \<sigma>) s"
      using non_stuttering_preserved `context_invariant t \<sigma> \<gamma> \<theta> \<tau>'` unfolding context_invariant_def
      by (simp add: non_stuttering_preserved \<open>\<forall>s. non_stuttering (to_trans_raw_sig \<tau>') \<sigma> s\<close>)
    have ne: "next_event t \<tau>' \<sigma> = {s. (snd (next_time_world tw_conc, snd tw_conc)) s (fst (next_time_world tw_conc, snd tw_conc)) \<noteq>
      signal_of False (derivative_hist_raw ( (snd (next_time_world tw_conc, snd tw_conc))) (fst (next_time_world tw_conc, snd tw_conc))) s
       (fst (next_time_world tw_conc, snd tw_conc) - 1)}" (is "_ = ?complex")
    proof -
      have "?complex = {s.  (snd tw_conc) s (next_time_world tw_conc) \<noteq>
      signal_of False (derivative_hist_raw ( (snd tw_conc)) (next_time_world tw_conc)) s
       (next_time_world tw_conc - 1)}"
        by auto
      also have "... = {s. worldline_raw t \<sigma> \<theta> \<tau>' s (next_time t \<tau>') \<noteq>
                           signal_of False (derivative_hist_raw (worldline_raw t \<sigma> \<theta> \<tau>') (next_time t \<tau>')) s (next_time t \<tau>' - 1)}"
        using ` (snd tw_conc) = worldline_raw t \<sigma> \<theta> \<tau>'` `next_time_world tw_conc = next_time t \<tau>'`
        by auto
      also have "... = {s. worldline_raw t \<sigma> \<theta> \<tau>' s (next_time t \<tau>') \<noteq>  signal_of False (add_to_beh \<sigma> \<theta> t (next_time t \<tau>')) s (next_time t \<tau>' - 1)}"
      proof -
        have 0: "snd (worldline2 t \<sigma> \<theta> \<tau>') = worldline_raw t \<sigma> \<theta> \<tau>'"
          by (auto simp add: worldline2_def)
        have *: "... = worldline_raw (next_time t \<tau>') (next_state t \<tau>' \<sigma>) (add_to_beh \<sigma> \<theta> t (next_time t \<tau>')) (\<tau>'(next_time t \<tau>' := 0)) "
          using worldline_next_config_next_time[OF `context_invariant t \<sigma> \<gamma> \<theta> \<tau>'`] by auto
        have **: "snd (worldline2 (next_time t \<tau>') (next_state t \<tau>' \<sigma>) (add_to_beh \<sigma> \<theta> t (next_time t \<tau>')) (\<tau>' (next_time t \<tau>' := 0))) =
              worldline_raw (next_time t \<tau>') (next_state t \<tau>' \<sigma>) (add_to_beh \<sigma> \<theta> t (next_time t \<tau>')) (\<tau>'(next_time t \<tau>' := 0))"
          unfolding worldline2_def by auto
        have "\<And>s. signal_of False (derivative_hist_raw (worldline_raw t \<sigma> \<theta> \<tau>') (next_time t \<tau>')) s (next_time t \<tau>' - 1) =
                   signal_of False (add_to_beh \<sigma> \<theta> t (next_time t \<tau>')) s (next_time t \<tau>' - 1)"
          using hist_of_worldline ci unfolding context_invariant_def ** sym[OF *] 
          by (metis (no_types, hide_lams) "*" \<open>t < next_time t \<tau>'\<close>
          cancel_comm_monoid_add_class.diff_cancel diff_less less_imp_diff_less
          less_numeral_extra(1) signal_of_derivative_hist_raw worldline_raw_def)
        thus ?thesis
          by auto
      qed
      also have "... = {s. next_state t \<tau>' \<sigma> s \<noteq> signal_of False (add_to_beh \<sigma> \<theta> t (next_time t \<tau>')) s (next_time t \<tau>' - 1)}"
      proof -
        have "t \<le> next_time t \<tau>'"
          using next_time_at_least[OF `\<And>n. n \<le> t \<Longrightarrow> \<tau>' n = 0`] by auto
        hence "\<And>s. worldline_raw t \<sigma> \<theta> \<tau>' s (next_time t \<tau>') = signal_of (\<sigma> s) \<tau>' s (next_time t \<tau>')"
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
              using lookup  by (meson trans_some_signal_of')
            finally have "signal_of (\<sigma> s) \<tau>' s (next_time t \<tau>') = next_state t \<tau>' \<sigma> s"
              by auto }
          moreover
          { have " \<tau> t s = 0"
              using ` \<tau> t  = 0` by transfer' (auto simp add: zero_fun_def zero_option_def zero_option_def)
            have "\<And>n. n < t \<Longrightarrow>  \<tau>' n  = 0"
              using `context_invariant t \<sigma> \<gamma> \<theta> \<tau>'` unfolding context_invariant_def by auto
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
              using \<open>next_state t \<tau>' \<sigma> s = \<sigma> s\<close> by blast }
          ultimately show " signal_of (\<sigma> s) \<tau>' s (next_time t \<tau>') = next_state t \<tau>' \<sigma> s"
            by auto
        qed
        ultimately have "\<And>s. worldline_raw t \<sigma> \<theta> \<tau>' s (next_time t \<tau>') = next_state t \<tau>' \<sigma> s"
          by auto
        thus ?thesis by auto
      qed
      also have "... = {s. next_state t \<tau>' \<sigma> s \<noteq> \<sigma> s}"
      proof -
        have "t \<le> next_time t \<tau>'"
          using \<open>\<And>n. n \<le> t \<Longrightarrow>  \<tau>' n = 0\<close> next_time_at_least  by (simp add: next_time_at_least)
        moreover have "\<And>n. t \<le> n \<Longrightarrow>  \<theta> n = 0"
          using `context_invariant t \<sigma> \<gamma> \<theta> \<tau>` unfolding context_invariant_def by auto
        ultimately have "\<And>s n. t < n \<Longrightarrow> n \<le> next_time t \<tau>' - 1 \<Longrightarrow> (add_to_beh \<sigma> \<theta> t (next_time t \<tau>')) n s = 0"
          unfolding add_to_beh_def by (simp add: lookup_update zero_fun_def)
        hence "t \<le> next_time t \<tau>' - 1"
          using `t < next_time t \<tau>'` by auto
        { fix s
          have "signal_of False (add_to_beh \<sigma> \<theta> t (next_time t \<tau>')) s (next_time t \<tau>' - 1) =
                signal_of False (add_to_beh \<sigma> \<theta> t (next_time t \<tau>')) s t"
            using `t \<le> next_time t \<tau>' - 1`
            by (metis (full_types) \<open>\<And>s n. \<lbrakk>t < n; n \<le> next_time t \<tau>' - 1\<rbrakk> \<Longrightarrow> (add_to_beh \<sigma> \<theta> t (next_time t \<tau>')) n s = 0\<close> le_neq_implies_less signal_of_less_ind')
          also have "... =  signal_of False (\<theta>(t:= Some o \<sigma>)) s t"
            using `t < next_time t \<tau>'` unfolding add_to_beh_def by auto
          also have "... = \<sigma> s"
            by (meson fun_upd_same trans_some_signal_of)
          finally have "signal_of False (add_to_beh \<sigma> \<theta> t (next_time t \<tau>')) s (next_time t \<tau>' - 1) = \<sigma> s"
            by auto }
        hence "\<And>s. signal_of False (add_to_beh \<sigma> \<theta> t (next_time t \<tau>')) s (next_time t \<tau>' - 1) = \<sigma> s"
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
    case (2 t maxtime \<tau> \<gamma> \<sigma> \<theta> cs)
    hence "\<forall>n. t \<le> n \<longrightarrow>  \<theta> n = 0"
      unfolding context_invariant_def by auto
    have "worldline2 t \<sigma> \<theta> \<tau> = (t, worldline_of_history (\<theta>(t := Some \<circ> \<sigma>)))"
    proof
      show "fst (worldline2 t \<sigma> \<theta> \<tau>) = fst (t, worldline_of_history  (\<theta>(t := Some \<circ> \<sigma>)))"
        using `tw = worldline2 t \<sigma> \<theta> \<tau>` by auto
    next
      have "worldline_raw t \<sigma> \<theta> \<tau> = signal_of False  (\<theta>(t := Some \<circ> \<sigma>))"
      proof (intro ext)+
        fix s' t'
        have "t' < t \<or> t \<le> t'" by auto
        moreover
        { assume "t' < t"
          hence *: "\<And>n. n < t \<Longrightarrow>  (to_trans_raw_sig  (\<theta>(t := Some \<circ> \<sigma>)) s') n = (to_trans_raw_sig \<theta> s') n"
            by (auto simp add:to_trans_raw_sig_def)
          hence "inf_time (to_trans_raw_sig  (\<theta>(t := Some \<circ> \<sigma>))) s' t' = inf_time (to_trans_raw_sig \<theta>) s' t'"
            by (meson \<open>t' < t\<close> inf_time_equal_when_same_trans_upto_strict)
          hence "signal_of False  (\<theta>(t := Some \<circ> \<sigma>)) s' t' = signal_of False \<theta> s' t'"
            unfolding to_signal_def comp_def using `t' < t`
            by (auto dest!: inf_time_at_most split:option.splits simp add: to_trans_raw_sig_def)
          hence " worldline_raw t \<sigma> \<theta> \<tau> s' t' = signal_of False  (\<theta>(t := Some \<circ> \<sigma>)) s' t'"
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
          ultimately have "signal_of (\<sigma> s') \<tau> s' t' = signal_of False (\<theta>(t := Some \<circ> \<sigma>)) s' t'"
            using inf_none unfolding to_signal_def comp_def 
            by (simp add: inf_time_def)
          hence " worldline_raw t \<sigma> \<theta> \<tau> s' t' = signal_of False (\<theta>(t := Some \<circ> \<sigma>)) s' t'"
            unfolding worldline_raw_def using `t \<le> t'` by auto }
        ultimately show "worldline_raw t \<sigma> \<theta> \<tau> s' t' = signal_of False (\<theta>(t := Some \<circ> \<sigma>)) s' t'"
          by auto
      qed
      thus "snd (worldline2 t \<sigma> \<theta> \<tau>) = snd (t, worldline_of_history  (\<theta>(t := Some \<circ> \<sigma>)))"
        unfolding worldline2_def  by (simp add: worldline_of_history_def)
    qed
    hence tw_def: "tw = (t, worldline_of_history (\<theta>(t:= Some o \<sigma>)))"
      using `tw = worldline2 t \<sigma> \<theta> \<tau>` by auto
    have *: "\<forall>tw'. tw, cs \<Rightarrow>\<^sub>c tw' \<longrightarrow> next_time_world tw' = fst tw + 1 \<and> snd tw = snd tw'"
    proof (rule, rule)
      fix tw'
      assume "tw, cs \<Rightarrow>\<^sub>c tw'"
      hence "fst tw = fst tw'"
        using fst_world_conc_exec by blast
      hence "fst tw' = t"
        using tw_def by auto
      obtain theta where des: "destruct_worldline tw = (t, \<sigma>, \<gamma>, theta, \<tau>)"
        and "\<And>k s. signal_of False \<theta> s k = signal_of False theta s k"
        using 2(3) destruct_worldline_correctness[OF 2(4)] transaction_worldline2
        by (metis (no_types, lifting) "2.prems"(2) "2.prems"(8) context_invariant_def
            derivative_raw_of_worldline2 destruct_worldline_def)
      have "b_conc_exec t \<sigma> \<gamma> theta cs \<tau> = b_conc_exec t \<sigma> \<gamma> \<theta> cs \<tau>"
        using `quiet \<tau> \<gamma>`  by (metis b_conc_exec_empty_event quiet_def)
      hence "tw' = tw"
        using `tw, cs \<Rightarrow>\<^sub>c tw'` des `tw = worldline2 t \<sigma> \<theta> \<tau>`
        unfolding world_conc_exec_def Let_def 
        by (metis (mono_tags, lifting) "2.hyps"(2) b_conc_exec_empty_event
        destruct_worldline_no_trans_at_t fun_upd_idem prod.simps(2) quiet_def
        worldline2_constructible_rem_curr_trans)
      have "derivative_raw (snd tw') (fst tw') = \<tau>"
        unfolding `tw' = tw` using `tw = worldline2 t \<sigma> \<theta> \<tau>` 2(4) unfolding context_invariant_def
        using derivative_raw_of_worldline2[OF _ _ 2(10)] by simp
      thus "next_time_world tw' = fst tw + 1 \<and> snd tw = snd tw'"
        using 2(2) unfolding next_time_world_def Let_def `fst tw' = t` quiet_def next_time_def
        using \<open>fst tw' = t\<close> \<open>tw' = tw\<close> by auto
    qed
    hence "P (fst tw + 1, snd tw)"
      using 2(6) `P tw` tw_def by (metis (mono_tags) conc_hoare_valid_def)
    { fix time 
      assume "time > fst tw"
      have "\<forall>tw'. (time, snd tw), cs \<Rightarrow>\<^sub>c tw' \<longrightarrow> next_time_world tw' = time + 1 \<and> snd tw = snd tw'"
      proof (rule, rule)
        fix tw'
        assume "(time, snd tw), cs \<Rightarrow>\<^sub>c tw'"
        hence "time = fst tw'"
          using fst_world_conc_exec by fastforce
        have "\<tau> = 0"
          using \<open>quiet \<tau> \<gamma>\<close> unfolding quiet_def by meson
        have "\<forall>n \<ge> t. \<theta> n = 0" and "\<forall>n \<le> t. \<tau> n = 0"
          using \<open>context_invariant t \<sigma> \<gamma> \<theta> \<tau>\<close> unfolding context_invariant_def by auto 
        hence "\<exists>theta. destruct_worldline (time, snd tw) = (time, \<sigma>, {}, theta, \<tau>) \<and> 
               (\<forall>k s. signal_of False (\<theta>(t := Some o \<sigma>)) s k = signal_of False theta s k)"
        proof -
          have *: "destruct_worldline (time, snd tw) = (time, \<sigma>, {}, derivative_hist_raw (snd tw) time, \<tau>)"
          proof -
            have "snd tw = worldline_of_history (\<theta>(t := Some \<circ> \<sigma>))"
              using tw_def by auto
            have "\<theta> time = 0"
              using `time > fst tw` \<open>\<forall>n \<ge> t. \<theta> n = 0\<close> by (simp add: "2.prems"(1))
            { fix s 
              have "snd tw s time = signal_of False (\<theta> (t:=Some o \<sigma>)) s time"
                using \<open>snd tw = worldline_of_history (\<theta>(t := Some \<circ> \<sigma>))\<close> 
                unfolding worldline_of_history_def by auto
              also have "... = signal_of False (\<theta> (t:=Some o \<sigma>)) s time"
                using signal_of_less[of "\<theta>(t := Some o \<sigma>)" "t + 1"] by simp
              also have "... = \<sigma> s"
                by (metis "2.prems"(1) \<open>\<tau> = 0\<close> \<open>fst tw < time\<close> \<open>snd tw = worldline_of_history (\<theta>(t :=
                Some \<circ> \<sigma>))\<close> \<open>worldline2 t \<sigma> \<theta> \<tau> = (t, worldline_of_history (\<theta>(t := Some \<circ> \<sigma>)))\<close>
                comp_def fst_conv less_trans nat_less_le prod.inject signal_of_empty
                worldline2_def worldline_of_history_def worldline_raw_def)
              hence "snd tw s time = \<sigma> s"
                using \<open>snd tw s time = signal_of False (\<theta>(t := Some \<circ> \<sigma>)) s time\<close> by blast }
            note * = this
            hence "(\<lambda>s. snd tw s time) = \<sigma>"
              by auto
            hence 1: "(\<lambda>s. snd (time, snd tw) s (fst (time, snd tw))) = \<sigma>"
              by auto
            have 2: "{s. snd tw s time \<noteq> signal_of False (derivative_hist_raw (snd tw) time) s t} = {}"
              using * 
              by (smt Collect_empty_eq \<open>fst tw < time\<close> \<open>snd tw = worldline_of_history (\<theta>(t := Some \<circ> \<sigma>))\<close> fst_conv fun_upd_same signal_of_derivative_hist_raw trans_some_signal_of tw_def worldline_of_history_def)
            { fix s n
              assume "n \<ge> time"
              have "snd tw s n = signal_of False (\<theta> (t:=Some o \<sigma>)) s n"
                using \<open>snd tw = worldline_of_history (\<theta>(t := Some \<circ> \<sigma>))\<close> 
                unfolding worldline_of_history_def by auto
              also have "... = signal_of False (\<theta> (t := Some o \<sigma>)) s time"
                using \<open>n \<ge> time\<close> 
                by (intro signal_of_less_ind')
                   (metis \<open>\<forall>n\<ge>t. \<theta> n = 0\<close> \<open>fst tw < time\<close> dual_order.trans fst_conv fun_upd_apply leD
                   order.strict_implies_order tw_def zero_fun_def)
              also have "... = snd tw s time"
                using \<open>snd tw = worldline_of_history (\<theta>(t := Some \<circ> \<sigma>))\<close> 
                unfolding worldline_of_history_def by auto          
              finally have "snd tw s n = snd tw s time"
                by auto }
            hence 3: "derivative_raw (snd tw) time = \<tau>"
              using derivative_raw_alt_def[where tw="(time, snd tw)"] \<open>\<tau> = 0\<close>
              by (metis fst_conv snd_conv)
            with 1 2 show ?thesis
              unfolding destruct_worldline_def Let_def
              by (smt Collect_empty_eq \<open>\<forall>n\<ge>t. \<theta> n = 0\<close> \<open>fst tw < time\<close> diff_less fst_conv
              fun_upd_other leI nat_less_le not_less_zero prod.sel(2) signal_of_derivative_hist_raw
              signal_of_less tw_def worldline_of_history_def zero_less_one)
          qed
          { fix k s
            have "signal_of False (\<theta>(t := Some o \<sigma>)) s k = signal_of False (derivative_hist_raw (snd tw) time) s k"
            proof -
              have "k \<le> time \<or> time < k"
                by auto
              moreover
              { assume "k \<le> time"
                hence "signal_of False (\<theta>(t := Some o \<sigma>)) s k = signal_of False (derivative_hist_raw (snd tw) time) s k"
                  using \<open>fst tw < time\<close>
                  by (metis (no_types, lifting) \<open>\<forall>n\<ge>t. \<theta> n = 0\<close> diff_diff_cancel diff_is_0_eq' fst_eqD
                  fun_upd_other le_neq_implies_less less_imp_le_nat not_gr_zero
                  signal_of_derivative_hist_raw signal_of_derivative_hist_raw2 signal_of_less_sig
                  snd_eqD tw_def worldline_of_history_def zero_fun_def) }
              moreover
              { assume "time < k"
                hence "t < k" and "time \<le> k"
                  using \<open>fst tw < time\<close> tw_def by auto
                hence " inf_time (to_trans_raw_sig (\<theta>(t := Some o \<sigma>))) s k = Some t"
                  by (meson \<open>\<forall>n\<ge>t. \<theta> n = 0\<close> \<open>t < k\<close> inf_time_update less_or_eq_imp_le)
                hence "signal_of False (\<theta>(t := Some o \<sigma>)) s k = \<sigma> s"
                  unfolding to_signal_def comp_def  by (simp add: to_trans_raw_sig_def)
                have "signal_of False (derivative_hist_raw (snd tw) time) s k = snd tw s (time - 1)"
                  using signal_of_derivative_hist_raw2[OF `time \<le> k`]
                  by (smt \<open>fst tw < time\<close> neq0_conv not_less_zero)
                also have "... = worldline_of_history (\<theta>(t:= Some o \<sigma>)) s t"
                  unfolding tw_def 
                  by (smt "*" \<open>\<forall>n\<ge>t. \<theta> n = 0\<close> \<open>fst tw < time\<close> destruct_worldline_def fst_conv
                  fun_upd_apply nat_neq_iff order.strict_implies_order signal_of_less snd_conv
                  trans_some_signal_of tw_def worldline_of_history_def)
                also have "... = signal_of False (\<theta>(t:= Some o \<sigma>)) s t"
                  unfolding worldline_of_history_def by auto
                finally have "signal_of False (\<theta>(t := Some o \<sigma>)) s k = signal_of False (derivative_hist_raw (snd tw) time) s k"
                  by (meson \<open>signal_of False (\<theta>(t := Some \<circ> \<sigma>)) s k = \<sigma> s\<close> fun_upd_same trans_some_signal_of)
              }
              ultimately show "signal_of False (\<theta>(t := Some o \<sigma>)) s k = signal_of False (derivative_hist_raw (snd tw) time) s k"
                by auto 
            qed }
          with * show ?thesis
            by auto
        qed
        then obtain theta where des: "destruct_worldline (time, snd tw) = (time, \<sigma>, {}, theta, \<tau>)"
          and "\<And>k s. signal_of False (\<theta>(t:= Some o \<sigma>)) s k = signal_of False theta s k"
          by blast
        have "b_conc_exec time \<sigma> {} theta cs \<tau> = b_conc_exec t \<sigma> \<gamma> \<theta> cs \<tau>"
          using `quiet \<tau> \<gamma>`  by (metis b_conc_exec_empty_event quiet_def)
        have "(time, snd tw) = tw'"
          using `(time, snd tw), cs \<Rightarrow>\<^sub>c tw'` des `tw = worldline2 t \<sigma> \<theta> \<tau>`
          unfolding world_conc_exec_def Let_def
          by (metis (mono_tags, lifting) b_conc_exec_empty_event fst_conv prod.case_eq_if snd_conv worldline2_constructible)
        hence "derivative_raw (snd tw') (fst tw') = \<tau>"
          by (metis (no_types, lifting) Pair_inject des destruct_worldline_def)
        thus " next_time_world tw' = time + 1 \<and> snd tw = snd tw'"
          using 2(2) unfolding next_time_world_def Let_def
          using \<open>(time, snd tw) = tw'\<close> \<open>\<tau> = 0\<close> by force
      qed }
    hence "\<And>time. time > fst tw \<Longrightarrow> \<forall>tw'. (time, snd tw), cs \<Rightarrow>\<^sub>c tw' \<longrightarrow> next_time_world tw' = time + 1 \<and> snd tw = snd tw'"
      by auto
    with * have **: "\<And>time. time \<ge> fst tw \<Longrightarrow> \<forall>tw'. (time, snd tw), cs \<Rightarrow>\<^sub>c tw' \<longrightarrow> next_time_world tw' = time + 1 \<and> snd tw = snd tw'"
      by (metis (full_types) dual_order.order_iff_strict prod.collapse)
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
      with 2(6) show ?case
        using `P (maxtime - 1, snd tw)` 
        by (metis (no_types, lifting) conc_hoare_valid_def)
    qed
    have "P (maxtime + 1, snd tw)"
      by (smt "**" "2.hyps"(1) "2.prems"(4) \<open>P (maxtime, snd tw)\<close> conc_hoare_valid_def fst_conv tw_def)
    moreover have "snd tw =  worldline_raw (maxtime + 1) \<sigma> (\<theta>(t := Some \<circ> \<sigma>)) 0"
      unfolding tw_def snd_conv 
    proof (rule ext)+
      fix s' t'
      have "t' < maxtime + 1 \<or> maxtime + 1 \<le> t'"
        by auto
      moreover
      { assume "t' < maxtime + 1"
        hence "worldline_raw (maxtime + 1) \<sigma> (\<theta>(t := Some \<circ> \<sigma>)) 0 s' t' = signal_of False (\<theta>(t := Some \<circ> \<sigma>)) s' t'"
          unfolding worldline_raw_def by auto
        also have "... = worldline_of_history (\<theta>(t := Some \<circ> \<sigma>)) s' t'"
          unfolding worldline_of_history_def by auto
        finally have "worldline_of_history (\<theta>(t:= Some o \<sigma>)) s' t' = worldline_raw (maxtime + 1) \<sigma> (\<theta>(t := Some \<circ> \<sigma>)) 0 s' t'"
          by auto }
      moreover
      { assume " maxtime + 1 \<le> t'"
        hence "worldline_raw (maxtime + 1) \<sigma> (\<theta>(t := Some \<circ> \<sigma>)) 0 s' t' = signal_of (\<sigma> s') 0 s' t'"
          unfolding worldline_raw_def by auto
        also have "... = \<sigma> s'"
          by (meson signal_of_empty)
        also have "... = signal_of False (\<theta>(t := Some \<circ> \<sigma>)) s' t"
          by (meson fun_upd_same trans_some_signal_of)
        also have "... = signal_of False (\<theta>(t := Some o \<sigma>)) s' t'"
          using \<open>\<forall>n. t \<le> n \<longrightarrow>  \<theta> n = 0\<close> \<open>t \<le> maxtime\<close> \<open>maxtime + 1 \<le> t'\<close> 
          by (intro sym[OF signal_of_less_ind'])(simp add: zero_fun_def, linarith)          
        also have "... = worldline_of_history (\<theta>(t:= Some o \<sigma>)) s' t'"
          unfolding worldline_of_history_def by auto
        finally have "worldline_of_history (\<theta>(t:= Some o \<sigma>)) s' t' = worldline_raw (maxtime + 1) \<sigma> (\<theta>(t := Some \<circ> \<sigma>)) 0 s' t'"
          by auto }
      ultimately show "worldline_of_history (\<theta>(t:= Some o \<sigma>)) s' t' = worldline_raw (maxtime + 1) \<sigma> (\<theta>(t := Some \<circ> \<sigma>)) 0 s' t'"
          by auto
    qed
    ultimately show ?case
      using "2.prems"(3) snd_conv tw_def
      by (simp add: \<open>tw' = (get_time (maxtime + 1, \<sigma>, \<theta>(t := Some \<circ> \<sigma>), 0), worldline_raw (get_time
      (maxtime + 1, \<sigma>, \<theta>(t := Some \<circ> \<sigma>), 0)) (get_state (maxtime + 1, \<sigma>, \<theta>(t := Some \<circ> \<sigma>), 0))
      (get_beh (maxtime + 1, \<sigma>, \<theta>(t := Some \<circ> \<sigma>), 0)) (get_trans (maxtime + 1, \<sigma>, \<theta>(t := Some \<circ> \<sigma>),
      0)))\<close>)
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

definition world_init_exec :: "nat \<times> 'signal worldline \<Rightarrow> 'signal conc_stmt \<Rightarrow> nat \<times> 'signal worldline" where
  "world_init_exec tw cs = (let (t , \<sigma> , \<gamma> , \<theta>, \<tau> ) = destruct_worldline tw;
                                                \<tau>'  = init' t \<sigma> \<gamma> \<theta> cs \<tau>
                            in 
                                 worldline2 t \<sigma> \<theta> \<tau>')"

abbreviation world_init_exec_abb :: "nat \<times> 'signal worldline \<Rightarrow> 'signal conc_stmt \<Rightarrow> nat \<times> 'signal worldline \<Rightarrow> bool"
  ("(_ , _) \<Rightarrow>\<^sub>I _")
  where "world_init_exec_abb tw s w' \<equiv> (world_init_exec tw s = w')"

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
  fix tw tw':: "nat \<times> 'a worldline"
  assume "P tw \<and> tw , c1 || c2 \<Rightarrow>\<^sub>I tw'"
  hence "P tw" and "tw, c1 || c2 \<Rightarrow>\<^sub>I tw'"
    by auto
  then obtain t \<sigma> \<gamma> \<theta> \<tau> \<tau>' where des: "destruct_worldline tw = (t, \<sigma>, \<gamma>, \<theta>, \<tau>)" and
    *: "init' t \<sigma> \<gamma> \<theta> (c1 || c2) \<tau> = \<tau>'" and w'_def: "worldline2 t \<sigma> \<theta> \<tau>' = tw'" and
    ci: "context_invariant t \<sigma> \<gamma> \<theta> \<tau>"
    unfolding world_init_exec_def Let_def  using destruct_worldline_exist
    by (auto simp add: worldline2_constructible split:prod.splits)
  define \<tau>1 where "\<tau>1 = init' t \<sigma> \<gamma> \<theta> c1 \<tau>"
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
      using init'_preserves_non_stuttering[OF sym[OF \<tau>1_def]] by auto
  qed
  hence ci1: "context_invariant t \<sigma> \<gamma> \<theta> \<tau>1"
    using init'_preserves_context_invariant[OF ci] assms(4) 
    by (simp add: \<tau>1_def)
  define \<tau>2 where "\<tau>2 = init' t \<sigma> \<gamma> \<theta> c2 \<tau>"
  hence ci2: "context_invariant t \<sigma> \<gamma> \<theta> \<tau>2"
    using init'_preserves_context_invariant[OF ci] assms(4) by auto
  have \<tau>'_def: "\<tau>' = init' t \<sigma> \<gamma> \<theta> c2 \<tau>1"
    using init'_sequential[OF assms(3)] * unfolding \<tau>1_def by auto
  define tw1 where "tw1 = worldline2 t \<sigma> \<theta> \<tau>1"
  have "tw, c1 \<Rightarrow>\<^sub>I tw1"
    using des \<tau>1_def unfolding world_init_exec_def Let_def by (simp add: tw1_def)
  hence "R tw1"
    using assms(1) `P tw` unfolding init_hoare_valid_def by blast
  obtain theta1 tau1 where des2: "destruct_worldline tw1 = (t, \<sigma>, \<gamma>, theta1, tau1)" and
    beh_same: "\<And>k s. signal_of False \<theta> s k = signal_of False theta1 s k" and
    trans_same: "\<And>k s. signal_of (\<sigma> s) \<tau>1 s k = signal_of (\<sigma> s) tau1 s k"
    using destruct_worldline_exist[of "worldline2 t \<sigma> \<theta> \<tau>1"] unfolding tw1_def
    using destruct_worldline_correctness[OF ci1] by metis
  have "context_invariant t \<sigma> \<gamma> theta1 tau1"
    using des2 worldline2_constructible by fastforce
  moreover have "nonneg_delay_conc c2"
    using assms(4) by auto
  ultimately have "worldline2 t \<sigma> theta1 (init' t \<sigma> \<gamma> theta1 c2 tau1) = worldline2 t \<sigma> \<theta> \<tau>'"
    using beh_same trans_same \<tau>'_def ci1  
  proof -
    have "\<And>k s. signal_of (\<sigma> s) (init' t \<sigma> \<gamma> theta1 c2 tau1) s k =
          signal_of (\<sigma> s) (init' t \<sigma> \<gamma> \<theta> c2 \<tau>1) s k"
      using helper_init'[OF _ beh_same trans_same] `context_invariant t \<sigma> \<gamma> theta1 tau1` 
      destruct_worldline_ensure_non_stuttering[OF des2] `\<forall>s. non_stuttering (to_trans_raw_sig \<tau>1) \<sigma> s`
      ci1 unfolding context_invariant_def  by (simp add: \<open>nonneg_delay_conc c2\<close>)
    thus ?thesis
      unfolding worldline2_def worldline_raw_def \<tau>'_def  using beh_same 
      by auto
  qed
  hence "tw1, c2 \<Rightarrow>\<^sub>I tw'"
    using des2   by (simp add: w'_def world_init_exec_def)
  with `R tw1` show "Q tw'"
    using assms(2) using init_hoare_valid_def by metis
qed

lemma parallelI_comp_commute':
  assumes "conc_stmt_wf (cs1 || cs2)"
  assumes "init' t \<sigma> \<gamma> \<theta> (cs1 || cs2) \<tau> = \<tau>'"
  shows "init' t \<sigma> \<gamma> \<theta> (cs2 || cs1) \<tau> = \<tau>'"
proof -
  have "disjnt (set (signals_from cs1)) (set (signals_from cs2))"
    using assms(1) unfolding conc_stmt_wf_def by (simp add: disjnt_def)
  thus ?thesis
    using van_tassel_second_prop' assms(2) by fastforce
qed

lemma world_init_exec_commute:
  assumes "tw, (cs1 || cs2) \<Rightarrow>\<^sub>I tw1"
  assumes "tw, (cs2 || cs1) \<Rightarrow>\<^sub>I tw2"
  assumes "conc_stmt_wf (cs1 || cs2)"
  shows "tw1 = tw2"
proof -
  obtain t \<sigma> \<gamma> \<theta> \<tau> \<tau>' where "destruct_worldline tw = (t, \<sigma>, \<gamma>, \<theta>, \<tau>)" and
    "init' t \<sigma> \<gamma> \<theta> (cs1 || cs2) \<tau> = \<tau>'" and "worldline2 t \<sigma> \<theta> \<tau>' = tw1"
    using assms(1) unfolding world_init_exec_def Let_def by (auto split:prod.splits)
  hence "init' t \<sigma> \<gamma> \<theta> (cs2 || cs1) \<tau> = \<tau>'"
    using parallelI_comp_commute'[OF assms(3)] by auto
  thus ?thesis
    using assms(2) unfolding world_init_exec_def Let_def
    using \<open>destruct_worldline tw = (t, \<sigma>, \<gamma>, \<theta>, \<tau>)\<close> \<open>worldline2 t \<sigma> \<theta> \<tau>' = tw1\<close>  by auto
qed

lemma soundness_init_hoare:
  assumes "\<turnstile>\<^sub>I \<lbrace>P\<rbrace> c \<lbrace>Q\<rbrace>"
  assumes "conc_stmt_wf c" and "nonneg_delay_conc c"
  shows "\<Turnstile>\<^sub>I \<lbrace>P\<rbrace> c \<lbrace>Q\<rbrace>"
  using assms
proof (induction rule:init_hoare.induct)
  case (SingleI P ss Q sl)
  { fix tw  tw' :: "nat \<times> 'a worldline"
    assume as: "P tw \<and> (tw ,  process sl : ss \<Rightarrow>\<^sub>I tw')"
    then obtain t \<sigma> \<gamma> \<theta> \<tau> \<tau>' where des: "destruct_worldline tw = (t, \<sigma>, \<gamma>, \<theta>, \<tau>)" and "P tw" and
      ex: "init' t \<sigma> \<gamma> \<theta> (process sl : ss) \<tau> = \<tau>'" and "(worldline2 t \<sigma> \<theta> \<tau>') = tw'"
      unfolding world_conc_exec_def Let_def 
      by (smt case_prod_conv destruct_worldline_exist world_init_exec_def)
    have "fst tw = t"
      by (metis (no_types, lifting) des destruct_worldline_def fst_conv)
    have "nonneg_delay ss"
      using SingleI by auto
    have "tw, ss \<Rightarrow>\<^sub>s tw'"
      using des unfolding world_seq_exec_def Let_def
      using \<open>worldline2 t \<sigma> \<theta> \<tau>' = tw'\<close> ex by auto
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
    using world_init_exec_commute[OF _ _ ParallelI2(3)]  
    by (metis init_hoare_valid_def)
next
  case (ConseqI P' P c Q Q')
  then show ?case by (metis init_hoare_valid_def)
next
  case (ConjI P cs Q1 Q2)
  hence "\<Turnstile>\<^sub>I \<lbrace>P\<rbrace> cs \<lbrace>Q1\<rbrace>" and "\<Turnstile>\<^sub>I \<lbrace>P\<rbrace> cs \<lbrace>Q2\<rbrace>"
    by blast+
  then show ?case 
    unfolding init_hoare_valid_def by blast
qed

definition init_sim :: "nat \<times> 'signal worldline \<Rightarrow> 'signal conc_stmt \<Rightarrow> nat \<times> 'signal worldline" 
  where "init_sim tw cs = (let tw' = world_init_exec tw cs in (next_time_world tw', snd tw'))"

definition init_sim_valid :: "'signal assn2 \<Rightarrow> 'signal conc_stmt \<Rightarrow> 'signal assn2 \<Rightarrow> bool" where
  "init_sim_valid P cs Q = (\<forall>tw tw'. P tw \<and> init_sim tw cs = tw' \<longrightarrow> Q tw')"

inductive
  init_sim_hoare :: "'signal assn2 \<Rightarrow> 'signal conc_stmt \<Rightarrow> 'signal assn2 \<Rightarrow> bool" where
AssignI: "\<turnstile>\<^sub>I \<lbrace>P\<rbrace> cs \<lbrace>\<lambda>tw. Q (next_time_world tw, snd tw)\<rbrace>  \<Longrightarrow> init_sim_hoare P cs Q" |
ConseqI_sim: "\<forall>tw. P' tw \<longrightarrow> P tw \<Longrightarrow> init_sim_hoare P cs Q \<Longrightarrow> \<forall>tw. Q tw \<longrightarrow> Q' tw \<Longrightarrow> init_sim_hoare P' cs Q'" | 
ConjI_sim: "init_sim_hoare P cs Q1 \<Longrightarrow> init_sim_hoare P cs Q2 \<Longrightarrow> init_sim_hoare P cs (\<lambda>tw. Q1 tw \<and> Q2 tw)"

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
    have "init_sim tw cs = (next_time_world tw', snd tw')" (is ?imp2)
      using \<open>tw, cs \<Rightarrow>\<^sub>I tw'\<close> unfolding init_sim_def Let_def by auto
    hence "?imp1 \<and> ?imp2"
      using \<open>?imp1\<close> by auto }
  then show ?case 
    unfolding init_sim_valid_def by presburger
next
  case (ConseqI_sim P' P cs Q Q')
  then show ?case  by (metis init_sim_valid_def)
next
  case (ConjI_sim P cs Q1 Q2)
  then show ?case  by (simp add: init_sim_valid_def)
qed

subsection \<open>Complete simulation = @{term "init_sim"} + @{term "world_sim_fin"}\<close>
                                                                      
inductive sim_fin :: "'signal worldline \<Rightarrow> nat \<Rightarrow> 'signal conc_stmt \<Rightarrow> nat \<times> 'signal worldline \<Rightarrow> bool" 
  where 
  "init_sim (0, w) cs = tw  \<Longrightarrow> tw, T, cs \<Rightarrow>\<^sub>S tw' \<Longrightarrow> sim_fin w T cs tw'"

inductive_cases sim_fin_ic: "sim_fin w T cs tw'"

lemma premises_sim_fin:
  assumes "sim_fin w T cs tw'"
  shows "\<exists>tw. init_sim (0, w) cs = tw \<and> tw, T, cs \<Rightarrow>\<^sub>S tw'"
  using sim_fin_ic[OF assms(1)] by blast

lemma premises_sim_fin_obt:
  assumes "sim_fin w T cs tw'"
  obtains tw where "init_sim (0, w) cs = tw" and "tw, T, cs \<Rightarrow>\<^sub>S tw'"
  using premises_sim_fin[OF assms] by blast

end