(*
 * Copyright 2019, NTU
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 *  Author: Albert Rizaldi, NTU Singapore
 *)

theory Multiplexer_Hoare2
  imports VHDL_Hoare_Complete Multiplexer_Hoare
begin

definition mux2' :: "sig conc_stmt" where
  "mux2' = process {IN0, IN1, SEL} : Bassign_trans OUT (Bwhen (Bsig IN1) (Bsig SEL) (Bsig IN0)) 1"

lemma only_if_disjnt:
  assumes "b_conc_exec t \<sigma> \<gamma> \<theta> def mux2' \<tau> \<tau>'"
  assumes "\<not> disjnt {IN0, IN1, SEL} \<gamma>"
  shows   "b_conc_exec t \<sigma> \<gamma> \<theta> def mux2  \<tau> \<tau>'"
  unfolding mux2_def
proof (intro b_conc_exec.intros(2))
  have " t , \<sigma> , \<gamma> , \<theta>, def  \<turnstile> Bsig SEL \<longrightarrow>\<^sub>b Bv True \<or>  t , \<sigma> , \<gamma> , \<theta>, def  \<turnstile> Bsig SEL \<longrightarrow>\<^sub>b Bv False"
    by (metis assms(1) assms(2) beval_cases(20) conc_cases(1) mux2'_def seq_cases(4))
  moreover
  { assume True: "t , \<sigma> , \<gamma> , \<theta>, def  \<turnstile> Bsig SEL \<longrightarrow>\<^sub>b Bv True"
    have "t , \<sigma> , \<gamma> , \<theta>, def  \<turnstile> <(Bassign_trans OUT (Bsig IN1) 1), \<tau>> \<longrightarrow>\<^sub>s (trans_post_raw OUT (\<sigma> IN1) (\<sigma> OUT) \<tau> t 1)"
      by (meson b_seq_exec.intros(5) beval_raw.intros(1))
    also have "... = \<tau>'"
      using assms(1-2) True unfolding mux2'_def 
      by (meson b_conc_exec.intros(2) b_conc_exec_deterministic b_seq_exec.intros(5)
      beval_raw.intros(1) beval_raw.intros(32))
    finally have "t , \<sigma> , \<gamma> , \<theta>, def  \<turnstile> <Bguarded (Bsig SEL) (Bassign_trans OUT (Bsig IN1) 1) (Bassign_trans OUT (Bsig IN0) 1) , \<tau>> \<longrightarrow>\<^sub>s \<tau>'"
      using True  by (simp add: b_seq_exec.intros(3)) }
  moreover
  { assume False: "t , \<sigma> , \<gamma> , \<theta>, def  \<turnstile> Bsig SEL \<longrightarrow>\<^sub>b Bv False"
    have "t , \<sigma> , \<gamma> , \<theta>, def  \<turnstile> <(Bassign_trans OUT (Bsig IN0) 1), \<tau>> \<longrightarrow>\<^sub>s (trans_post_raw OUT (\<sigma> IN0) (\<sigma> OUT) \<tau> t 1)"
      by (meson b_seq_exec.intros(5) beval_raw.intros(1))
    also have "... = \<tau>'"
      using assms(1-2) False unfolding mux2'_def
      by (metis beval_cases(1) beval_cases(20) conc_cases(1) seq_cases(4) val.inject(1))
    finally have "t , \<sigma> , \<gamma> , \<theta>, def  \<turnstile> <Bguarded (Bsig SEL) (Bassign_trans OUT (Bsig IN1) 1) (Bassign_trans OUT (Bsig IN0) 1) , \<tau>> \<longrightarrow>\<^sub>s \<tau>'"
      using False  by (simp add: b_seq_exec.intros(4)) }
  ultimately show "t , \<sigma> , \<gamma> , \<theta>, def  \<turnstile> <Bguarded (Bsig SEL) (Bassign_trans OUT (Bsig IN1) 1) (Bassign_trans OUT (Bsig IN0) 1) , \<tau>> \<longrightarrow>\<^sub>s \<tau>'"
    by metis
  show "\<not> disjnt {IN0, IN1, SEL} \<gamma>"
    using assms by auto
qed 

lemma only_if:
  assumes "b_conc_exec t \<sigma> \<gamma> \<theta> def mux2' \<tau> \<tau>'"
  shows   "b_conc_exec t \<sigma> \<gamma> \<theta> def mux2  \<tau> \<tau>'"
  using assms unfolding mux2'_def
  by (metis assms b_conc_exec.intros(1) conc_cases(1) mux2_def only_if_disjnt)

lemma whenever_disjnt:
  assumes "b_conc_exec t \<sigma> \<gamma> \<theta> def mux2  \<tau> \<tau>'"
  assumes "\<not> disjnt {IN0, IN1, SEL} \<gamma>"
  shows   "b_conc_exec t \<sigma> \<gamma> \<theta> def mux2' \<tau> \<tau>'"
  unfolding mux2'_def
proof (intro b_conc_exec.intros(2))
  have "t , \<sigma> , \<gamma> , \<theta>, def  \<turnstile> Bsig SEL \<longrightarrow>\<^sub>b Bv True \<or> t , \<sigma> , \<gamma> , \<theta>, def  \<turnstile> Bsig SEL \<longrightarrow>\<^sub>b Bv False"
    by (metis assms(1) assms(2) conc_cases(1) mux2_def seq_cases(3))
  moreover
  { assume True: "t , \<sigma> , \<gamma> , \<theta>, def  \<turnstile> Bsig SEL \<longrightarrow>\<^sub>b Bv True"
    hence "b_seq_exec t \<sigma> \<gamma> \<theta> def (Bassign_trans OUT (Bsig IN1) 1) \<tau> \<tau>'"
      using assms(1) 
      by (metis assms(2) beval_cases(1) conc_cases(1) mux2_def seq_cases(3) val.inject(1))
    hence "... = trans_post_raw OUT (\<sigma> IN1) (\<sigma> OUT) \<tau> t 1"
      by auto
    have "t , \<sigma> , \<gamma> , \<theta>, def  \<turnstile> Bwhen (Bsig IN1) (Bsig SEL) (Bsig IN0) \<longrightarrow>\<^sub>b \<sigma> IN1"
      by (simp add: True beval_raw.intros(1) beval_raw.intros(32))
    hence "t , \<sigma> , \<gamma> , \<theta>, def  \<turnstile> <Bassign_trans OUT (Bwhen (Bsig IN1) (Bsig SEL) (Bsig IN0)) 1 , \<tau>> \<longrightarrow>\<^sub>s \<tau>'"
      by (metis \<open>\<tau>' = trans_post_raw OUT (\<sigma> IN1) (\<sigma> OUT) \<tau> t 1\<close> b_seq_exec.intros(5)) }
  moreover
  { assume False: "t , \<sigma> , \<gamma> , \<theta>, def  \<turnstile> Bsig SEL \<longrightarrow>\<^sub>b Bv False"
    hence "b_seq_exec t \<sigma> \<gamma> \<theta> def (Bassign_trans OUT (Bsig IN0) 1) \<tau> \<tau>'"
      using assms(1) 
      by (metis assms(2) beval_cases(1) conc_cases(1) mux2_def seq_cases(3) val.inject(1))
    hence "... = trans_post_raw OUT (\<sigma> IN0) (\<sigma> OUT) \<tau> t 1"
      by auto
    have "t , \<sigma> , \<gamma> , \<theta>, def  \<turnstile> Bwhen (Bsig IN1) (Bsig SEL) (Bsig IN0) \<longrightarrow>\<^sub>b \<sigma> IN0"
      by (simp add: False beval_raw.intros(1) beval_raw.intros(33))
    hence "t , \<sigma> , \<gamma> , \<theta>, def  \<turnstile> <Bassign_trans OUT (Bwhen (Bsig IN1) (Bsig SEL) (Bsig IN0)) 1 , \<tau>> \<longrightarrow>\<^sub>s \<tau>'"
      by (metis \<open>\<tau>' = trans_post_raw OUT (\<sigma> IN0) (\<sigma> OUT) \<tau> t 1\<close> b_seq_exec.intros(5)) }
  ultimately show "t , \<sigma> , \<gamma> , \<theta>, def  \<turnstile> <Bassign_trans OUT (Bwhen (Bsig IN1) (Bsig SEL) (Bsig IN0)) 1 , \<tau>> \<longrightarrow>\<^sub>s \<tau>'"
    by metis
  show "\<not> disjnt {IN0, IN1, SEL} \<gamma>"
    using assms by auto
qed

lemma whenever:
  assumes "b_conc_exec t \<sigma> \<gamma> \<theta> def mux2  \<tau> \<tau>'"
  shows   "b_conc_exec t \<sigma> \<gamma> \<theta> def mux2' \<tau> \<tau>'"
  using whenever_disjnt 
  by (metis assms b_conc_exec.intros(1) b_conc_exec_deterministic mux2'_def mux2_def)

lemma b_conc_exec_mux2_eq_mux2':
  "b_conc_exec t \<sigma> \<gamma> \<theta> def mux2 \<tau> = b_conc_exec t \<sigma> \<gamma> \<theta> def mux2' \<tau>"
  using only_if whenever by auto

lemma init'_mux2_eq_mux2':
  "init' t \<sigma> \<gamma> \<theta> def mux2 \<tau> = init' t \<sigma> \<gamma> \<theta> def mux2' \<tau>"
proof (rule, rule)
  fix \<tau>'
  assume " init' t \<sigma> \<gamma> \<theta> def mux2 \<tau> \<tau>'"
  hence  *: "t, \<sigma>, \<gamma>, \<theta>, def  \<turnstile> < Bguarded (Bsig SEL)
                                      (Bassign_trans OUT (Bsig IN1) 1)
                                      (Bassign_trans OUT (Bsig IN0) 1), \<tau>> \<longrightarrow>\<^sub>s \<tau>'"
    unfolding mux2_def by auto
  hence "t , \<sigma> , \<gamma> , \<theta>, def  \<turnstile> (Bsig SEL) \<longrightarrow>\<^sub>b (Bv True) \<or> t , \<sigma> , \<gamma> , \<theta>, def  \<turnstile> (Bsig SEL) \<longrightarrow>\<^sub>b (Bv False)"
    by auto
  moreover
  { assume "t, \<sigma>, \<gamma>, \<theta>, def \<turnstile> (Bsig SEL) \<longrightarrow>\<^sub>b (Bv True)"
    hence "t, \<sigma>, \<gamma>, \<theta>, def \<turnstile> <Bassign_trans OUT (Bsig IN1) 1, \<tau>> \<longrightarrow>\<^sub>s \<tau>'"
      using *  by (metis beval_raw_deterministic seq_cases(3) val.inject(1))
    hence "t, \<sigma>, \<gamma>, \<theta>, def \<turnstile> <Bassign_trans OUT (Bwhen (Bsig IN1) (Bsig SEL) (Bsig IN0)) 1, \<tau>> \<longrightarrow>\<^sub>s \<tau>'"
      by (metis \<open>t , \<sigma> , \<gamma> , \<theta>, def \<turnstile> Bsig SEL \<longrightarrow>\<^sub>b Bv True\<close> b_seq_exec.intros(5)
      beval_raw.intros(32) seq_cases(4))
    hence "init' t \<sigma> \<gamma> \<theta> def mux2' \<tau> \<tau>'"
      by (simp add: init'.intros(1) mux2'_def) }
  moreover
  { assume "t, \<sigma>, \<gamma>, \<theta>, def \<turnstile> (Bsig SEL) \<longrightarrow>\<^sub>b (Bv False)"
    hence "t, \<sigma>, \<gamma>, \<theta>, def \<turnstile> <Bassign_trans OUT (Bsig IN0) 1, \<tau>> \<longrightarrow>\<^sub>s \<tau>'"
      using *  by (metis beval_raw_deterministic seq_cases(3) val.inject(1))
    hence "t, \<sigma>, \<gamma>, \<theta>, def \<turnstile> <Bassign_trans OUT (Bwhen (Bsig IN1) (Bsig SEL) (Bsig IN0)) 1, \<tau>> \<longrightarrow>\<^sub>s \<tau>'"
      by (metis \<open>t , \<sigma> , \<gamma> , \<theta>, def \<turnstile> Bsig SEL \<longrightarrow>\<^sub>b Bv False\<close> b_seq_exec.intros(5)
      beval_raw.intros(33) seq_cases(4))
    hence "init' t \<sigma> \<gamma> \<theta> def mux2' \<tau> \<tau>'"
      by (simp add: init'.intros(1) mux2'_def) }
  ultimately show "init' t \<sigma> \<gamma> \<theta> def mux2' \<tau> \<tau>'"
    by metis
next
  fix \<tau>'
  assume "init' t \<sigma> \<gamma> \<theta> def mux2' \<tau> \<tau>'"
  hence *: "t, \<sigma>, \<gamma>, \<theta>, def  \<turnstile> < Bassign_trans OUT (Bwhen (Bsig IN1) (Bsig SEL) (Bsig IN0)) 1, \<tau>> \<longrightarrow>\<^sub>s \<tau>'"
    unfolding mux2'_def  by blast 
  hence "t , \<sigma> , \<gamma> , \<theta>, def  \<turnstile> (Bsig SEL) \<longrightarrow>\<^sub>b (Bv True) \<or> t , \<sigma> , \<gamma> , \<theta>, def  \<turnstile> (Bsig SEL) \<longrightarrow>\<^sub>b (Bv False)"
    by auto
  moreover
  { assume "t, \<sigma>, \<gamma>, \<theta>, def \<turnstile> (Bsig SEL) \<longrightarrow>\<^sub>b (Bv True)"
    hence **: "t, \<sigma>, \<gamma>, \<theta>, def \<turnstile> (Bwhen (Bsig IN1) (Bsig SEL) (Bsig IN0)) \<longrightarrow>\<^sub>b (\<sigma> IN1)"
      by (simp add: beval_raw.intros(1) beval_raw.intros(32))
    hence "\<tau>' = trans_post_raw OUT (\<sigma> IN1) (\<sigma> OUT) \<tau> t 1"
      by (meson * b_seq_exec.intros(5) b_seq_exec_deterministic)
    hence "init' t \<sigma> \<gamma> \<theta> def mux2 \<tau> \<tau>'"
      by (metis ** b_seq_exec.intros(3) b_seq_exec.intros(4) b_seq_exec.intros(5) beval_cases(20) init'.intros(1) mux2_def) }
  moreover
  { assume "t, \<sigma>, \<gamma>, \<theta>, def \<turnstile> (Bsig SEL) \<longrightarrow>\<^sub>b (Bv False)"
    hence **: "t, \<sigma>, \<gamma>, \<theta>, def \<turnstile> (Bwhen (Bsig IN1) (Bsig SEL) (Bsig IN0)) \<longrightarrow>\<^sub>b (\<sigma> IN0)"
      by (simp add: beval_raw.intros(1) beval_raw.intros(33))
    hence "\<tau>' = trans_post_raw OUT (\<sigma> IN0) (\<sigma> OUT) \<tau> t 1"
      by (meson * b_seq_exec.intros(5) b_seq_exec_deterministic)
    hence "init' t \<sigma> \<gamma> \<theta> def mux2 \<tau> \<tau>'"
      by (metis ** b_seq_exec.intros(3) b_seq_exec.intros(4) b_seq_exec.intros(5) beval_cases(20) init'.intros(1) mux2_def) }
  ultimately show "init' t \<sigma> \<gamma> \<theta> def mux2 \<tau> \<tau>'"
    by metis
qed

lemma b_simulate_fin_only_if':
  assumes "maxtime, t, \<sigma>, \<gamma>, \<theta>, def \<turnstile> <cs , \<tau>> \<leadsto> tres"
  assumes "cs = mux2"
  shows   "maxtime, t, \<sigma>, \<gamma>, \<theta>, def \<turnstile> <mux2', \<tau>> \<leadsto> tres"
  using assms
proof (induction rule:b_simulate_fin.inducts)
  case (1 t maxtime \<tau> \<gamma> \<sigma> \<theta> def cs \<tau>' res)
  then show ?case 
    by (simp add: "1.IH" b_conc_exec_mux2_eq_mux2' b_simulate_fin.intros(1))
next
  case (2 t maxtime \<tau> \<gamma> \<sigma> \<theta> def cs)
  then show ?case 
    using b_simulate_fin.intros(2) by blast
next
  case (3 t maxtime \<sigma> \<gamma> \<theta> def cs \<tau>)
  then show ?case 
    by (simp add: b_simulate_fin.intros(3))
qed

lemma b_simulate_fin_only_if:
  assumes "maxtime, t, \<sigma>, \<gamma>, \<theta>, def \<turnstile> <mux2 , \<tau>> \<leadsto> tres"
  shows   "maxtime, t, \<sigma>, \<gamma>, \<theta>, def \<turnstile> <mux2', \<tau>> \<leadsto> tres"
  using b_simulate_fin_only_if' assms by auto

lemma b_simulate_fin_whenever':
  assumes "maxtime, t, \<sigma>, \<gamma>, \<theta>, def \<turnstile> <cs, \<tau>> \<leadsto> tres"
  assumes "cs = mux2'"
  shows   "maxtime, t, \<sigma>, \<gamma>, \<theta>, def \<turnstile> <mux2 , \<tau>> \<leadsto> tres"
  using assms
  apply (induction rule:b_simulate_fin.inducts)
  by (simp add: b_conc_exec_mux2_eq_mux2' b_simulate_fin.intros(1))
     (blast intro: b_simulate_fin.intros)+

lemma b_simulate_fin_whenever:
  assumes "maxtime, t, \<sigma>, \<gamma>, \<theta>, def \<turnstile> <mux2', \<tau>> \<leadsto> tres"
  shows   "maxtime, t, \<sigma>, \<gamma>, \<theta>, def \<turnstile> <mux2 , \<tau>> \<leadsto> tres"
  using assms b_simulate_fin_whenever' by auto

lemma b_simulate_mux2_eq_mux2':
  "b_simulate_fin maxtime t \<sigma> \<gamma> \<theta> def mux2 \<tau> = b_simulate_fin maxtime t \<sigma> \<gamma> \<theta> def mux2' \<tau>"
  using b_simulate_fin_whenever b_simulate_fin_only_if by auto

lemma world_sim_fin_only_if:
  assumes "tw, T, mux2 \<Rightarrow>\<^sub>S tw'"
  shows   "tw, T, mux2' \<Rightarrow>\<^sub>S tw'"
  using assms 
  by (simp add: b_simulate_mux2_eq_mux2' world_sim_fin.simps)

lemma world_sim_fin_whenever:
  assumes "tw, T, mux2' \<Rightarrow>\<^sub>S tw'"
  shows   "tw, T, mux2 \<Rightarrow>\<^sub>S tw'"
  using assms 
  by (simp add: b_simulate_mux2_eq_mux2' world_sim_fin.simps)

lemma world_sim_fin_mux2_eq_mux2':
  "world_sim_fin tw T mux2 = world_sim_fin tw T mux2'"
  using world_sim_fin_only_if world_sim_fin_whenever by blast

lemma init_sim_only_if:
  assumes "init_sim tw mux2  tw'"
  shows   "init_sim tw mux2' tw'"
  using assms 
  by (simp add: init'_mux2_eq_mux2' init_sim.simps world_init_exec.simps)

lemma init_sim_whenever:
  assumes "init_sim tw mux2' tw'"
  shows   "init_sim tw mux2  tw'"
  using assms 
  by (simp add: init'_mux2_eq_mux2' init_sim.simps world_init_exec.simps)

lemma init_sim_mux2_eq_mux2':
  "init_sim tw mux2 = init_sim tw mux2'"
  apply (rule)+
  apply (erule init_sim_only_if)
  apply (erule init_sim_whenever)
  done

lemma sim_fin_only_if:
  assumes "sim_fin w T mux2  tw'"
  shows   "sim_fin w T mux2' tw'"
  using assms
  by (simp add: init_sim_mux2_eq_mux2' sim_fin.simps world_sim_fin_mux2_eq_mux2')

lemma sim_fin_whenever:
  assumes "sim_fin w T mux2' tw'"
  shows   "sim_fin w T mux2  tw'"
  using assms
  by (simp add: init_sim_mux2_eq_mux2' sim_fin.simps world_sim_fin_mux2_eq_mux2')

lemma sim_fin_mux2_eq_mux2':
  "sim_fin w T mux2 = sim_fin w T mux2'"
  apply (rule, rule)
  apply (erule sim_fin_only_if)
  apply (erule sim_fin_whenever)
  done

lemma mux2'_correctness:
  assumes "sim_fin w (i + 1) mux2' tw'" and "wityping \<Gamma> w"
  assumes "conc_wt \<Gamma> mux2"
  shows "wline_of tw' OUT (i + 1) = (if bval_of_wline tw' SEL i then wline_of tw' IN1 i else wline_of tw' IN0 i)"
  using mux2_correctness sim_fin_mux2_eq_mux2' assms by auto

end