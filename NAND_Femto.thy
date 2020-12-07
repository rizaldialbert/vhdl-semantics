(*
 * Copyright 2018-2019, NTU
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 *  Author: Albert Rizaldi, NTU Singapore
 *)

theory NAND_Femto
imports
  Femto_VHDL Femto_VHDL_Executable
begin

lemma trans_post_empty_trans_upd:
  "trans_post sig v def empty_trans t dly =
    (if v \<noteq> def then Poly_Mapping.update (t + dly) [sig \<mapsto> v] empty_trans else empty_trans)"
proof transfer'
  fix sig :: "'a"
  fix v def t dly
  have "post_necessary_raw (dly) (\<lambda>k. 0) t sig v def \<or> \<not> post_necessary_raw (dly) (\<lambda>k. 0) t sig v def"
    by auto
  moreover
  { assume nec: "post_necessary_raw (dly) (\<lambda>k. 0) t sig v def"
    hence "v \<noteq> def"
      by (metis post_necessary_raw_correctness zero_fun_def zero_option_def)
    hence "(if post_necessary_raw (dly) (\<lambda>k. 0) t sig v def then post_raw sig v (\<lambda>k. 0) (t + dly) else preempt_raw sig (\<lambda>k. 0) (t + dly)) =
      (if v \<noteq> def then (\<lambda>k. 0)(t + dly := [sig \<mapsto> v]) else (\<lambda>k. 0))"
      using nec unfolding trans_post_raw_def post_raw_def preempt_raw_def zero_upd zero_map fun_upd_def
      by auto }
  moreover
  { assume not_nec: "\<not> post_necessary_raw (dly) (\<lambda>k. 0) t sig v def"
    hence "v = def"
      unfolding post_necessary_raw_correctness 
      by (metis option.distinct(1) zero_fun_def zero_option_def)
    hence "(if post_necessary_raw (dly) (\<lambda>k. 0) t sig v def then post_raw sig v (\<lambda>k. 0) (t + dly) else preempt_raw sig (\<lambda>k. 0) (t + dly)) =
      (if v \<noteq> def then (\<lambda>k. 0)(t + dly := [sig \<mapsto> v]) else (\<lambda>k. 0))"
      using not_nec by (auto simp add: preempt_raw_def zero_fun_def zero_option_def) }
  ultimately have " (if post_necessary_raw (dly) (\<lambda>k. 0) t sig v def then post_raw sig v (\<lambda>k. 0) (t + dly) else preempt_raw sig (\<lambda>k. 0) (t + dly)) =
       (if v \<noteq> def then (\<lambda>k. 0)(t + dly := [sig \<mapsto> v]) else (\<lambda>k. 0))" by auto
  thus "trans_post_raw sig v def (\<lambda>k. 0) t dly = (if v \<noteq> def then (\<lambda>k. 0)(t + dly := [sig \<mapsto> v]) else (\<lambda>k. 0)) "
    unfolding trans_post_raw_def by auto
qed

lemma get_trans_trans_upd_cancel:
  "lookup (Poly_Mapping.update n [sig \<mapsto> v] \<tau>) n = [sig \<mapsto> v]"
  by transfer auto

definition nand :: "sig conc_stmt" where
  "nand = process {A, B} : Bassign_inert C (Bnand (Bsig A) (Bsig B)) 1"

code_thms simulate_fin

code_thms functional_simulate_fin

values  "{lookup (get_beh beh) 1 C | beh. simulate_fin_ind 10 0 (\<lambda>x. Bv False) {A} 0 (\<lambda>x. Bv False) nand empty_trans beh}"

value " ((lookup o get_beh) (functional_simulate_fin 10 0 (\<lambda>x. Bv False) {A} 0 (\<lambda>x. Bv False) nand 0)) 1 C"

theorem
  "(lookup o get_beh) (functional_simulate_fin 10 0 (\<lambda>x. Bv False) {A} 0 (\<lambda>x. Bv False) nand empty_trans) 1 C = Some (Bv True)"
  by eval

value "(lookup o get_beh) (functional_simulate 10 (\<lambda>x. Bv False) nand empty_trans) 1 C"

value "signal_of2 (Bv False) (get_beh (functional_simulate 10 (\<lambda>x. Bv False) nand empty_trans)) C 100"

value [code] "to_signal (Bv False) (to_transaction_sig (empty_trans :: nat \<Rightarrow>\<^sub>0 sig \<rightharpoonup> val)) A 123456"

hide_const Femto_VHDL.next_time Femto_VHDL.next_state Femto_VHDL.next_event Femto_VHDL.add_to_beh
           Femto_VHDL.quiet Femto_VHDL.inf_time Femto_VHDL.init' Femto_VHDL.to_signal
hide_fact  Femto_VHDL.next_time_def Femto_VHDL.next_state_def Femto_VHDL.next_event_def
           Femto_VHDL.add_to_beh_def Femto_VHDL.quiet_def Femto_VHDL.to_signal_def Femto_VHDL.inf_time_def
           Femto_VHDL.init'_def

theorem
  assumes "10, 0, (\<lambda>x. Bv False), {A}, 0, (\<lambda>x. Bv False) \<turnstile> <nand, 0> \<leadsto> beh"
  shows "signal_of (Bv False) (get_beh beh) C (1::nat)  = (Bv True)"
  using assms
proof (cases)
  case (1 \<tau>')
  have temp0: "trans_post_raw C (Bv True) (Bv False) (override_on 0 (\<lambda>n. (0 n)(C := None)) {0<..Suc 0}) 0 (Suc 0) =
        0(Suc 0 := [C \<mapsto> Bv True])"
  proof -
    let ?\<tau> = "override_on 0 (\<lambda>n. (0 n)(C := None)) {0<..Suc 0}"
    have "signal_of (Bv False) ?\<tau> C 0 = (Bv False)"
      by (metis (no_types, lifting) greaterThanAtMost_iff less_irrefl_nat override_on_def
      signal_of_zero zero_fun_def)
    hence "post_necessary_raw (Suc 0) (override_on 0 (\<lambda>n. (0 n)(C := None)) {0<..Suc 0}) 0 C (Bv True) (Bv False)"
      by auto
    hence "trans_post_raw C (Bv True) (Bv False) ?\<tau> 0 (Suc 0) = post_raw C (Bv True) ?\<tau> (Suc 0)"
      unfolding trans_post_raw_def by auto
    also have "... = 0(Suc 0 := [C \<mapsto> Bv True])"
      unfolding post_raw_def by (auto simp add: zero_fun_def zero_option_def)
    finally show ?thesis
      by auto
  qed
  have "0 , (\<lambda>x. Bv False) , {A} , 0, (\<lambda>x. Bv False) \<turnstile> <Bassign_inert C (Bnand (Bsig A) (Bsig B)) 1 , 0> \<longrightarrow>\<^sub>s (0(1 := [C \<mapsto> Bv True]))"
  proof (intro b_seq_exec.intros)
    have "0 , \<lambda>x. Bv False , {A} , 0, \<lambda>x. Bv False  \<turnstile> Bnand (Bsig A) (Bsig B) \<longrightarrow>\<^sub>b Bv (\<not> (False \<and> False))"
      by (intro beval_raw.intros)
    thus " 0 , \<lambda>x. Bv False , {A} , 0, \<lambda>x. Bv False  \<turnstile> Bnand (Bsig A) (Bsig B) \<longrightarrow>\<^sub>b Bv True"
      by auto
  next
    have "signal_of (Bv False) 0 C 1 \<noteq> Bv True"
      by (metis signal_of_empty val.inject(1))
    hence "purge_raw' 0 0 1 C (Bv False) (Bv True) = override_on 0 (\<lambda>n. (0 n)(C := None)) {0<..Suc 0}"
      unfolding purge_raw'_def Let_def purge_raw_def by auto
    thus "inr_post_raw' C (Bv True) (Bv False) 0 0 1 = 0(1 := [C \<mapsto> Bv True])"
      using temp0 unfolding inr_post_raw'_def by auto
  qed
  hence "0 , (\<lambda>x. Bv False) , {A} , 0, (\<lambda>x. Bv False) \<turnstile> <get_seq nand , 0> \<longrightarrow>\<^sub>s (0(1 := [C \<mapsto> Bv True]))"
    unfolding nand_def by auto
  hence base: "0 , (\<lambda>x. Bv False) , {A} , 0, (\<lambda>x. Bv False) \<turnstile> <nand , 0> \<longrightarrow>\<^sub>c (0(1 := [C \<mapsto> Bv True]))"
    unfolding nand_def
    by (simp add: b_conc_exec.intros(2))
  hence \<tau>'_def: "\<tau>' = (0(1:=[C \<mapsto> Bv True]))"
    using 1  by (simp add: b_conc_exec_deterministic)
  have nt: "next_time 0 \<tau>' = 1"
  proof -
    have "(0(1:=[C \<mapsto> Bv True])) \<noteq> 0"
      by (metis fun_upd_same option.distinct(1) zero_fun_def zero_option_def)
    moreover have "(LEAST n. dom (\<tau>' n) \<noteq> {}) = 1"
      unfolding \<tau>'_def
    proof (rule Least_equality)
      show "dom ((0(1 := [C \<mapsto> Bv True])) 1) \<noteq> {}"
        by auto
    next
      { fix y :: nat
        assume "\<not> 1 \<le> y"
        hence "y = 0"
          by auto
        hence "dom (((\<lambda>_. 0)(1 := [C \<mapsto> Bv True])) y) = {}"
          by (auto simp add: zero_map)
        hence "\<not> dom (((\<lambda>_. 0)(1 := [C \<mapsto> Bv True])) y) \<noteq> {}"
          by auto
        hence "\<not> dom ((0(1 := [C \<mapsto> Bv True])) y) \<noteq> {}"
          by (simp add: zero_fun_def) }
      thus "\<And>y::nat.  dom ((0(1 := [C \<mapsto> Bv True])) y) \<noteq> {} \<Longrightarrow> 1 \<le> y"
        by fastforce
    qed
    ultimately show ?thesis
      unfolding \<tau>'_def next_time_def by auto
  qed
  have ns: "next_state 0 \<tau>' (\<lambda>x. Bv False) = (\<lambda>x. Bv False) (C := Bv True)" (is "?lhs = ?rhs")
    unfolding next_state_def Let_def nt
    by (simp add: \<tau>'_def override_on_insert')
  have ne: "next_event 0 \<tau>' (\<lambda>x. Bv False) = {C}"
  proof -
    {
      fix sig
      assume "sig \<in> dom (\<tau>' 1)"
      hence "sig = C"
        unfolding \<tau>'_def by transfer' auto
      hence "(the \<circ> \<tau>' 1) sig \<noteq> Bv False"
        unfolding \<tau>'_def by transfer' auto
      with `sig = C` have "sig = C" and "(the \<circ> \<tau>' 1) sig \<noteq> Bv False"
        by auto }
    hence "\<And>sig. sig \<in> dom (\<tau>' 1) \<Longrightarrow> (the o \<tau>' 1) sig \<noteq> Bv False \<Longrightarrow> sig = C"
      by auto
    hence "next_event 0 \<tau>' (\<lambda>x. Bv False) \<subseteq> {C}"
      unfolding next_event_def Let_def nt by auto
    have "C \<in> dom (\<tau>' 1)"
      unfolding \<tau>'_def by (simp add: get_trans_trans_upd_cancel)
    moreover have "(the \<circ> \<tau>' 1) C \<noteq> Bv False"
      unfolding \<tau>'_def  using \<open>\<And>sig. sig \<in> dom (\<tau>' 1) \<Longrightarrow> (the \<circ> \<tau>' 1) sig \<noteq> Bv False\<close>
      \<tau>'_def calculation by blast
    ultimately have "{C} \<subseteq> next_event 0 \<tau>' (\<lambda>x. Bv False)"
      unfolding next_event_def Let_def nt by auto
    with `next_event 0 \<tau>' (\<lambda>x. Bv False) \<subseteq> {C}` show ?thesis
      by auto
  qed
  have  add_to_beh2: "Femto_VHDL_raw.add_to_beh2 ((\<lambda>x. Bv False)(C := Bv True)) 0 1 (\<lambda>x. Bv False) =
       Femto_VHDL_raw.add_to_beh2 ((\<lambda>x. Bv False)(C := Bv True)) 0 1 (\<lambda>x. Bv False)" (is "_ = ?beh'")
    unfolding Femto_VHDL_raw.add_to_beh2_def fun_upd_def Let_def by auto
(*   proof (rule, rule)
    fix x :: nat
    fix s :: sig
    have "x = 1 \<or> x \<noteq> 1" by auto
    moreover
    { assume " x = 1"
      hence cont: "(if x = 1 then \<lambda>s. if signal_of (Bv False) 0 s 1 = (if s = C then Bv True else Bv False) then 0 (1::nat) s else Some (if s = C then Bv True else Bv False) else 0 x) s = 
             (if signal_of (Bv False) 0 s 1 = (if s = C then Bv True else Bv False) then 0 (1::nat) s else Some (if s = C then Bv True else Bv False))"
        by auto
      have "s = C \<or> s \<noteq> C"
        by auto
      moreover
      { assume "s = C"
        hence "(if signal_of (Bv False) 0 s 1 = (if s = C then Bv True else Bv False) then None else Some (if s = C then Bv True else Bv False)) = 
                Some (if s = C then Bv True else Bv False)"
          by (metis signal_of_empty val.inject(1))
        also have "... = (if x = 1 then \<lambda>x. if x = C then Some (Bv True) else None else 0 x) s"
          unfolding `x = 1` `s = C` by auto
        finally have "(if x = 1 then \<lambda>s. if signal_of (Bv False) 0 s 1 = (if s = C then Bv True else Bv False) then 0 (1::nat) s else Some (if s = C then Bv True else Bv False) else 0 x) s =
                     (if x = 1 then \<lambda>x. if x = C then Some (Bv True) else 0 (1::nat) s else 0 x) s"
          using cont by auto }
      moreover
      { assume " s \<noteq> C"
        hence "(if x = 1 then \<lambda>s. if signal_of (Bv False) 0 s 1 = (if s = C then Bv True else Bv False) then 0 (1::nat) s else Some (if s = C then Bv True else Bv False) else 0 x) s =
                     (if x = 1 then \<lambda>x. if x = C then Some (Bv True) else 0 (1::nat) s else 0 x) s"
          unfolding `x = 1` 
          using signal_of_empty by force }
      ultimately have "(if x = 1 then \<lambda>s. if signal_of (Bv False) 0 s 1 = (if s = C then Bv True else Bv False) then 0 (1::nat) s else Some (if s = C then Bv True else Bv False) else 0 x) s =
                       (if x = 1 then \<lambda>x. if x = C then Some (Bv True) else 0 (1::nat) s else 0 x) s"
        by blast }
    moreover
    { assume "x \<noteq> 1"
      hence "(if x = 1 then \<lambda>s. if signal_of (Bv False) 0 s 1 = (if s = C then Bv True else Bv False) then 0 (1::nat) s else Some (if s = C then Bv True else Bv False) else 0 x) s =
             (if x = 1 then \<lambda>x. if x = C then Some (Bv True) else 0 (1::nat) s else 0 x) s"
        by auto }
    ultimately show "(if x = 1 then \<lambda>s. if signal_of (Bv False) 0 s 1 = (if s = C then Bv True else Bv False) then 0 (1::nat) s else Some (if s = C then Bv True else Bv False) else 0 x) s =
                       (if x = 1 then \<lambda>x. if x = C then Some (Bv True) else 0 (1::nat) s else 0 x) s"
      by auto
  qed *)
  have "\<And>s. signal_of (Bv False) 0 s 0 = Bv False"
    by (meson signal_of_empty)
  hence nb:"Femto_VHDL_raw.add_to_beh2 (\<lambda>x. Bv False) 0 0 (\<lambda>x. Bv False) = 0"
    unfolding Femto_VHDL_raw.add_to_beh2_def fun_upd_def zero_option_def zero_fun_def Let_def
    by fastforce
  define beh2 :: "(nat \<Rightarrow> sig \<Rightarrow> val option)" where "beh2 = ?beh'"
  hence snd_cyc: "10, 1, (\<lambda>x. Bv False) (C := Bv True), {C} , 0, (\<lambda>x. Bv False) \<turnstile> <nand , (\<tau>'(1:=0))> \<leadsto> beh"
    using 1 nt ns ne nb by metis
  have " \<not> quiet (\<tau>'(1 := 0)) {C}"
    unfolding \<tau>'_def fun_upd_def quiet_def by auto
  then obtain \<tau>'' where ex2: "1 , (\<lambda>x. Bv False)(C := Bv True) , {C} , 0, \<lambda>x. Bv False  \<turnstile> <nand , \<tau>'(1 := 0)> \<longrightarrow>\<^sub>c \<tau>''"
    using bau[OF snd_cyc] \<open>\<not> quiet (\<tau>'(1 := 0)) {C}\<close> by fastforce
  have "\<tau>'(1:=0) = \<tau>''"
    using conc_cases(1)[OF ex2[unfolded nand_def]] by auto
  hence "next_time 1 \<tau>'' \<le> 10"
    unfolding \<tau>'_def next_time_def  by (simp add: fun_upd_idem zero_fun_def)
  hence thd_cyc: "10, next_time 1 \<tau>'' , next_state 1 \<tau>'' ((\<lambda>x. Bv False)(C := Bv True)) , next_event 1 \<tau>'' ((\<lambda>x. Bv False)(C := Bv True)) , beh2 , \<lambda>x. Bv False \<turnstile> <nand , \<tau>''(next_time 1 \<tau>'' := 0)> \<leadsto> beh"
    using  bau[OF snd_cyc] using beh2_def add_to_beh2
    by (metis \<open>\<not> quiet (\<tau>'(1 := 0)) {C}\<close> add_to_beh2 case_bau ex2 one_less_numeral_iff semiring_norm(76) snd_cyc)
  have "next_time 1 \<tau>'' = 2"
    using \<open>\<tau>'(1:=0) = \<tau>''\<close> unfolding \<tau>'_def next_time_def 
    by (metis fun_upd_idem_iff fun_upd_upd nat_1_add_1 zero_fun_def)
  hence "next_state 1 \<tau>'' ((\<lambda>x. Bv False)(C := Bv True)) = ((\<lambda>x. Bv False)(C := Bv True))"
    using \<open>\<tau>'(1:=0) = \<tau>''\<close> unfolding next_state_def Let_def 
    by (smt \<tau>'_def dom_eq_singleton_conv fun_upd_idem_iff fun_upd_upd next_state_def next_time_at_least2 next_time_def not_less_Least ns nt override_on_emptyset override_on_insert' zero_fun_def zero_less_one)
  have "next_event 1 \<tau>'' ((\<lambda>x. Bv False)(C := Bv True)) = {}"
    using \<open>\<tau>'(1:=0) = \<tau>''\<close> `next_time 1 \<tau>'' = 2` unfolding next_event_def Let_def \<tau>'_def
    by (smt Collect_empty_eq domIff fun_upd_other numeral_eq_one_iff semiring_norm(85) zero_fun_def zero_option_def)
  hence "10, 2, ((\<lambda>x. Bv False)(C := Bv True)), {}, beh2, \<lambda>x. Bv False \<turnstile> <nand , \<tau>''(next_time 1 \<tau>'' := 0)> \<leadsto> beh "
    using thd_cyc 
    using \<open>next_state 1 \<tau>'' ((\<lambda>x. Bv False)(C := Bv True)) = (\<lambda>x. Bv False)(C := Bv True)\<close> \<open>next_time 1 \<tau>'' = 2\<close> by auto
  thus "signal_of (Bv False) (get_beh beh) C 1 = Bv True"
  proof (cases)
    case (1 \<tau>x)
    thus ?thesis
      by (metis \<open>\<tau>'(1 := 0) = \<tau>''\<close> \<tau>'_def fun_upd_idem fun_upd_upd quiet_def zero_fun_def)
  next
    case (2 \<tau>x)
    then show ?thesis
      unfolding `beh2 = ?beh'` 
      by (metis \<open>\<tau>'(1 := 0) = \<tau>''\<close> \<tau>'_def fun_upd_idem fun_upd_upd quiet_def zero_fun_def)
  next
    case 3
    hence "get_beh beh = Femto_VHDL_raw.add_to_beh2 ((\<lambda>x. Bv False)(C := Bv True)) 0 (1::nat) (\<lambda>x. Bv False)"
      by (simp add: beh2_def)
    hence "signal_of (Bv False) (get_beh beh) C (1::nat) = signal_of (Bv False) (Femto_VHDL_raw.add_to_beh2 ((\<lambda>x. Bv False)(C := Bv True)) 0 (1::nat) (\<lambda>x. Bv False)) C (1::nat)"
      by auto
    also have "... = Bv True"
      unfolding Femto_VHDL_raw.add_to_beh2_def Let_def fun_upd_def 
    proof -
      have f1: "Bv False = signal_of (Bv False) 0 C 1"
        by (metis signal_of_empty)
      have "\<forall>f n s fa v. f n (s::sig) \<noteq> Some (fa s) \<or> signal_of v f s n = fa s"
        by (meson trans_some_signal_of')
      then show "signal_of (Bv False) (\<lambda>n. if n = 1 then \<lambda>s. if signal_of (Bv False) 0 s 1 = (if s = C then Bv True else Bv False) then 0 (1::nat) s else Some (if s = C then Bv True else Bv False) else 0 n) C 1 = Bv True"
        using f1 val.inject(1) by presburger
    qed
    finally show ?thesis
      by auto
  qed auto
next
  case (2 \<tau>')
  have temp0: "trans_post_raw C (Bv True) (Bv False) (override_on 0 (\<lambda>n. (0 n)(C := None)) {0<..Suc 0}) 0 (Suc 0) =
        0(Suc 0 := [C \<mapsto> Bv True])"
  proof -
    let ?\<tau> = "override_on 0 (\<lambda>n. (0 n)(C := None)) {0<..Suc 0}"
    have "signal_of (Bv False) ?\<tau> C 0 = (Bv False)"
      by (metis (no_types, lifting) greaterThanAtMost_iff less_irrefl_nat override_on_def
      signal_of_zero zero_fun_def)
    hence "post_necessary_raw (Suc 0) (override_on 0 (\<lambda>n. (0 n)(C := None)) {0<..Suc 0}) 0 C (Bv True) (Bv False)"
      by auto
    hence "trans_post_raw C (Bv True) (Bv False) ?\<tau> 0 (Suc 0) = post_raw C (Bv True) ?\<tau> (Suc 0)"
      unfolding trans_post_raw_def by auto
    also have "... = 0(Suc 0 := [C \<mapsto> Bv True])"
      unfolding post_raw_def by (auto simp add: zero_fun_def zero_option_def)
    finally show ?thesis
      by auto
  qed
  have "0 , (\<lambda>x. Bv False) , {A} , 0, (\<lambda>x. Bv False) \<turnstile> <Bassign_inert C (Bnand (Bsig A) (Bsig B)) 1 , 0> \<longrightarrow>\<^sub>s (0(1 := [C \<mapsto> Bv True]))"
  proof (intro b_seq_exec.intros)
    have "0 , \<lambda>x. Bv False , {A} , 0, \<lambda>x. Bv False  \<turnstile> Bnand (Bsig A) (Bsig B) \<longrightarrow>\<^sub>b Bv (\<not> (False \<and> False))"
      by (intro beval_raw.intros)
    thus " 0 , \<lambda>x. Bv False , {A} , 0, \<lambda>x. Bv False  \<turnstile> Bnand (Bsig A) (Bsig B) \<longrightarrow>\<^sub>b Bv True"
      by auto
  next
    have "signal_of (Bv False) 0 C 1 \<noteq> Bv True"
      by (metis signal_of_empty val.inject(1))
    hence "purge_raw' 0 0 1 C (Bv False) (Bv True) = override_on 0 (\<lambda>n. (0 n)(C := None)) {0<..Suc 0}"
      unfolding purge_raw'_def purge_raw_def Let_def by auto
    thus "inr_post_raw' C (Bv True) (Bv False) 0 0 1 = 0(1 := [C \<mapsto> Bv True])"
      using temp0 unfolding inr_post_raw'_def by auto
  qed
  hence "0 , (\<lambda>x. Bv False) , {A} , 0, (\<lambda>x. Bv False) \<turnstile> <get_seq nand , 0> \<longrightarrow>\<^sub>s (0(1 := [C \<mapsto> Bv True]))"
    unfolding nand_def by auto
  hence base: "0 , (\<lambda>x. Bv False) , {A} , 0, (\<lambda>x. Bv False) \<turnstile> <nand , 0> \<longrightarrow>\<^sub>c (0(1 := [C \<mapsto> Bv True]))"
    unfolding nand_def
    by (simp add: b_conc_exec.intros(2))
  hence \<tau>'_def: "\<tau>' = (0(1:=[C \<mapsto> Bv True]))"
    using 2  by (simp add: b_conc_exec_deterministic)
  have nt: "next_time 0 \<tau>' = 1"
  proof -
    have "(0(1:=[C \<mapsto> Bv True])) \<noteq> 0"
      by (metis fun_upd_same option.distinct(1) zero_fun_def zero_option_def)
    moreover have "(LEAST n. dom (\<tau>' n) \<noteq> {}) = 1"
      unfolding \<tau>'_def
    proof (rule Least_equality)
      show "dom ((0(1 := [C \<mapsto> Bv True])) 1) \<noteq> {}"
        by auto
    next
      { fix y :: nat
        assume "\<not> 1 \<le> y"
        hence "y = 0"
          by auto
        hence "dom (((\<lambda>_. 0)(1 := [C \<mapsto> Bv True])) y) = {}"
          by (auto simp add: zero_map)
        hence "\<not> dom (((\<lambda>_. 0)(1 := [C \<mapsto> Bv True])) y) \<noteq> {}"
          by auto
        hence "\<not> dom ((0(1 := [C \<mapsto> Bv True])) y) \<noteq> {}"
          by (simp add: zero_fun_def) }
      thus "\<And>y::nat.  dom ((0(1 := [C \<mapsto> Bv True])) y) \<noteq> {} \<Longrightarrow> 1 \<le> y"
        by fastforce
    qed
    ultimately show ?thesis
      unfolding \<tau>'_def next_time_def by auto
  qed
  then show ?thesis 
    using 2 by auto
next
  case 3
  then show ?thesis 
    by (simp add: quiet_def)
next
  case 4
  then show ?thesis by auto
qed

definition nand2 :: "sig conc_stmt" where
  "nand2 = process {A, B} : Bcomp
                            (Bassign_trans C (Bnand (Bsig A) (Bsig B)) 1)
                            (Bassign_trans A (Bnand (Bsig A) (Bsig B)) 3)"

definition "test_trans = Pm_fmap (fmap_of_list [(4::nat, [A \<mapsto> Bv True, B \<mapsto> Bv True])])"
definition  "test2 = functional_simulate_fin 2 0 (\<lambda>x. Bv False) {A, B, C} 0 (\<lambda>x. Bv False) nand2 test_trans"

value [code] "to_transaction_sig (get_beh test2) C"

definition nand4 :: "sig conc_stmt" where
  "nand4 = process {A, B} : Bassign_trans C (Bnand (Bsig A) (Bsig B)) 0"

\<comment> \<open>Specific lemmas about @{term "nand"} and @{term "nand3"}\<close>

lemma nand_does_not_modify_AB:
  assumes "b_seq_exec t \<sigma> \<gamma> \<theta> def (get_seq nand) \<tau> \<tau>'"
  shows "\<And>i. i \<ge> t \<Longrightarrow> s \<noteq> C \<Longrightarrow> \<tau> i s = \<tau>' i s"
  using b_seq_exec_modifies_local assms unfolding nand_def
  by (metis conc_stmt.sel(4) empty_set list.simps(15) signals_in.simps(3) singletonD)

lemma nand_does_not_modify_AB':
  assumes "\<And>n. n < t \<Longrightarrow>  \<tau> n = 0"
  assumes "b_seq_exec t \<sigma> \<gamma> \<theta> def (get_seq nand) \<tau> \<tau>'"
  shows "\<And>i. s \<noteq> C \<Longrightarrow> \<tau> i s =  \<tau>' i s"
  using assms unfolding nand_def
  by (metis assms(2) b_seq_exec_preserve_trans_removal nand_does_not_modify_AB not_le)

lemma maxtime_maxtime_bigstep:
  assumes "maxtime, maxtime, \<sigma>, \<gamma>, \<theta>, def \<turnstile> <nand3, \<tau>> \<leadsto> beh"
  shows "get_beh beh = \<theta>"
proof -
  have "(maxtime, \<sigma>, \<gamma>, \<theta>, \<tau>) = beh"
    using assms bau by blast
  then show ?thesis
    by force
qed 

lemma signal_of_add_to_beh2:
  assumes "t < split"
  assumes "\<forall>n > t. \<theta> n s = 0"
  shows "signal_of (def s) (Femto_VHDL_raw.add_to_beh2 \<sigma> \<theta> t def) s split = \<sigma> s"
proof (cases "inf_time (to_trans_raw_sig (Femto_VHDL_raw.add_to_beh2 \<sigma> \<theta> t def)) s split")
  case None
  hence "Femto_VHDL_raw.add_to_beh2 \<sigma> \<theta> t def t s = None"
    by (metis assms dual_order.strict_implies_order inf_time_noneE2 to_trans_raw_sig_def zero_option_def)
  hence " signal_of (def s) \<theta> s t = \<sigma> s"
    unfolding Femto_VHDL_raw.add_to_beh2_def fun_upd_def Let_def 
    by (smt option.simps(3))
  have inf_none2: "inf_time (to_trans_raw_sig (Femto_VHDL_raw.add_to_beh2 \<sigma> \<theta> t def)) s t = None"
    using None assms by (meson inf_time_none_iff order.strict_trans)
  hence cont: "inf_time (to_trans_raw_sig (Femto_VHDL_raw.add_to_beh2 \<sigma> \<theta> t def)) s t = inf_time (to_trans_raw_sig (Femto_VHDL_raw.add_to_beh2 \<sigma> \<theta> t def)) s (t - 1)"
    by (meson inf_time_less inf_time_noneE2 less_or_eq_imp_le)
  have "0 < t \<or> t = 0"
    by auto
  moreover
  { assume "0 < t"
    hence "inf_time (to_trans_raw_sig (Femto_VHDL_raw.add_to_beh2 \<sigma> \<theta> t def)) s (t - 1) = inf_time (to_trans_raw_sig \<theta>) s (t - 1)"
      unfolding Femto_VHDL_raw.add_to_beh2_def Let_def fun_upd_def 
      by (smt diff_less inf_time_equal_when_same_trans_upto leD order_refl zero_less_one)
    hence "inf_time (to_trans_raw_sig \<theta>) s (t - 1) = None"
      using None cont  using inf_none2 by auto
    hence " (def s  = \<sigma> s \<and> \<theta> t s = None)"
      using \<open>signal_of (def s) \<theta> s t = \<sigma> s\<close> 
      by (smt Femto_VHDL_raw.add_to_beh2_def \<open>Femto_VHDL_raw.add_to_beh2 \<sigma> \<theta> t def t s = None\<close>
      comp_apply fun_upd_same option.simps(4) signal_of_less_sig to_signal_def zero_option_def)
    moreover have "inf_time (to_trans_raw_sig (Femto_VHDL_raw.add_to_beh2 \<sigma> \<theta> t def)) s t = None"
      using inf_none2 by blast
    ultimately have " signal_of (def s) (Femto_VHDL_raw.add_to_beh2 \<sigma> \<theta> t def) s split = \<sigma> s"
      by (simp add: None to_signal_def) }
  moreover
  { assume "t = 0"
    have "signal_of (def s) (Femto_VHDL_raw.add_to_beh2 \<sigma> \<theta> t def) s split = \<sigma> s"
      by (smt Femto_VHDL_raw.add_to_beh2_def None \<open>Femto_VHDL_raw.add_to_beh2 \<sigma> \<theta> t def t s = None\<close>
      \<open>signal_of (def s) \<theta> s t = \<sigma> s\<close> \<open>t = 0\<close> comp_apply fun_upd_same inf_none2 signal_of_zero
      to_signal_def zero_option_def) }
  ultimately show "signal_of (def s) (Femto_VHDL_raw.add_to_beh2 \<sigma> \<theta> t def) s split = \<sigma> s"
    by auto
next
  case (Some a)
  have "a \<le> t"
  proof (rule ccontr)
    assume "\<not> a \<le> t" hence "t < a" by auto
    hence "(\<theta> a s) \<noteq> None"
      using Some 
    proof -
      have "\<forall>f fa n fb na. Femto_VHDL_raw.add_to_beh2 (f::'a \<Rightarrow> val) fb na fa n = fb n \<or> na = n"
        by (simp add: Femto_VHDL_raw.add_to_beh2_def)
      then show ?thesis
        by (metis Femto_VHDL_raw.keys_def \<open>\<not> a \<le> t\<close> \<open>inf_time (to_trans_raw_sig (Femto_VHDL_raw.add_to_beh2 \<sigma> \<theta> t def)) s split = Some a\<close> domIff dom_def inf_time_some_exists le_refl to_trans_raw_sig_def zero_option_def)
    qed
    thus False
      using assms `t < a`  by (simp add: zero_option_def)
  qed
  hence "a < t \<or> a = t"
    by auto
  moreover
  { assume " a = t"
    hence "Femto_VHDL_raw.add_to_beh2 \<sigma> \<theta> t def t s \<noteq> None"
      using inf_time_some_exists[OF Some]  unfolding Femto_VHDL_raw.keys_def to_trans_raw_sig_def
      by (simp add: zero_option_def)
    have "signal_of (def s) \<theta> s t = \<sigma> s \<or> signal_of (def s) \<theta> s t \<noteq> \<sigma> s"
      by auto
    moreover
    { assume "signal_of (def s) \<theta> s t \<noteq> \<sigma> s"
      hence "Femto_VHDL_raw.add_to_beh2 \<sigma> \<theta> t def t s = Some (\<sigma> s) "
        unfolding Femto_VHDL_raw.add_to_beh2_def Let_def fun_upd_def by auto
      hence ?thesis
        using Some `a = t` 
        by (metis comp_apply some_inf_time' to_signal_def trans_some_signal_of') }
    moreover
    { assume "signal_of (def s) \<theta> s t = \<sigma> s"
      hence "Femto_VHDL_raw.add_to_beh2 \<sigma> \<theta> t def t s = \<theta> t s "
        unfolding Femto_VHDL_raw.add_to_beh2_def Let_def fun_upd_def by auto
      with \<open>Femto_VHDL_raw.add_to_beh2 \<sigma> \<theta> t def t s \<noteq> None\<close> have "\<theta> t s = Some (\<sigma> s)"
        using \<open>signal_of (def s) \<theta> s t = \<sigma> s\<close> 
        by (metis le_refl nat_less_le signal_of_val_eq to_trans_raw_sig_def)
      hence ?thesis
        using Some `a = t` 
        by (simp add: \<open>Femto_VHDL_raw.add_to_beh2 \<sigma> \<theta> t def t s = \<theta> t s\<close> to_signal_def to_trans_raw_sig_def) }
    ultimately have ?thesis
      by auto }
  moreover
  { assume " a < t"
    with Some \<open>t < split\<close> have fnone: "Femto_VHDL_raw.add_to_beh2 \<sigma> \<theta> t def t s = None"
      using inf_time_someE[OF Some] 
      by (metis (full_types) domIff nat_less_le not_le to_trans_raw_sig_def)  
    hence "signal_of (def s) \<theta> s t = \<sigma> s"
      unfolding Femto_VHDL_raw.add_to_beh2_def Let_def fun_upd_def 
      by (smt option.distinct(1))
    have "Femto_VHDL_raw.add_to_beh2 \<sigma> \<theta> t def t s = \<theta> t s"
      using fnone unfolding Femto_VHDL_raw.add_to_beh2_def Let_def fun_upd_def
      using \<open>signal_of (def s) \<theta> s t = \<sigma> s\<close> by auto
    have "\<And>n. a < n \<Longrightarrow> n \<le> t \<Longrightarrow> \<theta> n s = 0"
    proof (rule ccontr)
      fix n 
      assume "a < n" and "n \<le> t" and "\<theta> n s \<noteq> 0"
      hence "\<theta> n s \<noteq> None"
        by (simp add: zero_option_def)
      hence "Femto_VHDL_raw.add_to_beh2 \<sigma> \<theta> t def n s \<noteq> None"
        by (metis (no_types, lifting) Femto_VHDL_raw.add_to_beh2_def \<open>Femto_VHDL_raw.add_to_beh2 \<sigma> \<theta> t def t s = \<theta> t s\<close> fun_upd_other)
      have a_def: "a = (GREATEST l. l \<in> Femto_VHDL_raw.keys (to_trans_raw_sig (Femto_VHDL_raw.add_to_beh2 \<sigma> \<theta> t def) s) \<and> l \<le> split)"
        using inf_time_when_exist[OF Some] by auto
      have "\<exists>l. l \<in> Femto_VHDL_raw.keys (to_trans_raw_sig (Femto_VHDL_raw.add_to_beh2 \<sigma> \<theta> t def) s) \<and> l \<le> split"
        by (meson Some inf_time_some_exists)
      have "n \<in> Femto_VHDL_raw.keys (to_trans_raw_sig (Femto_VHDL_raw.add_to_beh2 \<sigma> \<theta> t def) s)"
        using \<open>Femto_VHDL_raw.add_to_beh2 \<sigma> \<theta> t def n s \<noteq> None\<close> unfolding to_trans_raw_sig_def Femto_VHDL_raw.keys_def zero_option_def by auto
      hence "n \<le> a"
        using a_def 
        by (smt Femto_VHDL_raw.keys_def Some \<open>n \<le> t\<close> assms(1) domIff inf_time_someE le_less_trans mem_Collect_eq nat_less_le zero_option_def)
      with `a < n` show False
        by auto
    qed
    have Some2: "inf_time (to_trans_raw_sig (Femto_VHDL_raw.add_to_beh2 \<sigma> \<theta> t def)) s a = Some a"
    proof -
      have "0 \<noteq> to_trans_raw_sig (Femto_VHDL_raw.add_to_beh2 \<sigma> \<theta> t def) s a"
        using Femto_VHDL_raw.keys_def Some inf_time_some_exists by fastforce
      then have "\<exists>v. Some v = Femto_VHDL_raw.add_to_beh2 \<sigma> \<theta> t def a s"
        by (metis (no_types) option.exhaust_sel to_trans_raw_sig_def zero_option_def)
      then have "\<exists>f. Some (f s) = Femto_VHDL_raw.add_to_beh2 \<sigma> \<theta> t def a s"
        by meson
      then show ?thesis
        by (metis some_inf_time')
    qed
    have " signal_of (def s) (Femto_VHDL_raw.add_to_beh2 \<sigma> \<theta> t def) s split =  signal_of (def s) (Femto_VHDL_raw.add_to_beh2 \<sigma> \<theta> t def) s a"
      unfolding to_signal_def comp_def Some Some2 by auto
    also have "... = signal_of (def s) \<theta> s a"
      apply (rule signal_of_equal_when_trans_equal_upto[where maxtime="a"])
      using `a < t` unfolding Femto_VHDL_raw.add_to_beh2_def Let_def fun_upd_def by auto
    also have "... = signal_of (def s) \<theta> s t"
      apply (rule signal_of_less_ind'[THEN sym])
      using \<open>\<And>n. a < n \<Longrightarrow> n \<le> t \<Longrightarrow> \<theta> n s = 0\<close> \<open>a \<le> t\<close> by auto
    finally have ?thesis
      using \<open>signal_of (def s) \<theta> s t = \<sigma> s\<close> by auto }
  ultimately show ?thesis 
    by auto
qed

lemma signal_of_add_to_beh2':
  assumes "t \<le> split"
  assumes "\<forall>n > t. \<theta> n s = 0"
  shows "signal_of (def s) (Femto_VHDL_raw.add_to_beh2 \<sigma> \<theta> t def) s split = \<sigma> s"
proof (cases "t < split")
  case True
  then show ?thesis 
    using signal_of_add_to_beh2  by (metis assms(2))
next
  case False
  hence "t = split"
    using assms by auto
  then show ?thesis 
    using assms(2) 
    by (smt Femto_VHDL_raw.add_to_beh2_def eq_iff fun_upd_def le_imp_less_Suc signal_of_add_to_beh2 signal_of_suc_sig)
qed

lemma add_to_beh2_fixed_point:
  assumes "t < split"
  assumes "\<And>s. \<forall>n > t. \<theta> n s = 0"
  shows "Femto_VHDL_raw.add_to_beh2 \<sigma> (Femto_VHDL_raw.add_to_beh2 \<sigma> \<theta> t def) split def = Femto_VHDL_raw.add_to_beh2 \<sigma> \<theta> t def"
proof (rule)
  fix x :: nat
  have "x = split \<or> x < split \<or> x > split"
    by auto
  moreover
  { assume "x = split"
    have "Femto_VHDL_raw.add_to_beh2 \<sigma> (Femto_VHDL_raw.add_to_beh2 \<sigma> \<theta> t def) split def x = Femto_VHDL_raw.add_to_beh2 \<sigma> \<theta> t def split"
      unfolding Femto_VHDL_raw.add_to_beh2_def[where \<theta>="Femto_VHDL_raw.add_to_beh2 \<sigma> \<theta> t def"] Let_def
      `x = split` fun_upd_def using signal_of_add_to_beh2[where \<theta>="\<theta>", OF assms] by auto
    hence "Femto_VHDL_raw.add_to_beh2 \<sigma> (Femto_VHDL_raw.add_to_beh2 \<sigma> \<theta> t def) split def x = Femto_VHDL_raw.add_to_beh2 \<sigma> \<theta> t def x"
      using \<open>x = split\<close> by auto }
  moreover
  { assume "x > split"
    hence "Femto_VHDL_raw.add_to_beh2 \<sigma> (Femto_VHDL_raw.add_to_beh2 \<sigma> \<theta> t def) split def x = \<theta> x"
      unfolding Femto_VHDL_raw.add_to_beh2_def Let_def fun_upd_def
      using `t < split` by auto
    also have "... = Femto_VHDL_raw.add_to_beh2 \<sigma> \<theta> t def x"
      using \<open>x > split\<close> \<open>split > t\<close> unfolding Femto_VHDL_raw.add_to_beh2_def by auto
    finally have "Femto_VHDL_raw.add_to_beh2 \<sigma> (Femto_VHDL_raw.add_to_beh2 \<sigma> \<theta> t def) split def x = Femto_VHDL_raw.add_to_beh2 \<sigma> \<theta> t def x"
      by auto }
  moreover
  { assume "x < split"
    have "x < t \<or> x = t \<or> x > t"
      by auto
    moreover
    { assume "x > t"
      hence "Femto_VHDL_raw.add_to_beh2 \<sigma> (Femto_VHDL_raw.add_to_beh2 \<sigma> \<theta> t def) split def x = \<theta> x"
        using \<open>x < split\<close> unfolding Femto_VHDL_raw.add_to_beh2_def Let_def fun_upd_def by auto
      also have "... = Femto_VHDL_raw.add_to_beh2 \<sigma> \<theta> t def x"
        using `x > t` unfolding Femto_VHDL_raw.add_to_beh2_def fun_upd_def Let_def by auto
      finally have "Femto_VHDL_raw.add_to_beh2 \<sigma> (Femto_VHDL_raw.add_to_beh2 \<sigma> \<theta> t def) split def x = Femto_VHDL_raw.add_to_beh2 \<sigma> \<theta> t def x"
        by auto }
    moreover
    { assume "x < t"
      hence "Femto_VHDL_raw.add_to_beh2 \<sigma> (Femto_VHDL_raw.add_to_beh2 \<sigma> \<theta> t def) split def x = \<theta> x"
        using \<open>x < split\<close> unfolding Femto_VHDL_raw.add_to_beh2_def Let_def fun_upd_def by auto
      also have "... = Femto_VHDL_raw.add_to_beh2 \<sigma> \<theta> t def x"
        using `x < t` unfolding Femto_VHDL_raw.add_to_beh2_def fun_upd_def Let_def by auto
      finally have "Femto_VHDL_raw.add_to_beh2 \<sigma> (Femto_VHDL_raw.add_to_beh2 \<sigma> \<theta> t def) split def x = Femto_VHDL_raw.add_to_beh2 \<sigma> \<theta> t def x"
        by auto }
    moreover
    { assume "x = t"
      hence "Femto_VHDL_raw.add_to_beh2 \<sigma> (Femto_VHDL_raw.add_to_beh2 \<sigma> \<theta> t def) split def x = 
              (\<lambda>s. if to_signal (def s) (to_trans_raw_sig \<theta>) s t = \<sigma> s then \<theta> t s else Some (\<sigma> s))"
        using \<open>x < split\<close> unfolding Femto_VHDL_raw.add_to_beh2_def fun_upd_def Let_def by auto
      also have "... = Femto_VHDL_raw.add_to_beh2 \<sigma> \<theta> t def x"
        using \<open>x = t\<close> unfolding Femto_VHDL_raw.add_to_beh2_def fun_upd_def Let_def by auto
      finally have "Femto_VHDL_raw.add_to_beh2 \<sigma> (Femto_VHDL_raw.add_to_beh2 \<sigma> \<theta> t def) split def x = Femto_VHDL_raw.add_to_beh2 \<sigma> \<theta> t def x"
        by auto }
    ultimately have "Femto_VHDL_raw.add_to_beh2 \<sigma> (Femto_VHDL_raw.add_to_beh2 \<sigma> \<theta> t def) split def x = Femto_VHDL_raw.add_to_beh2 \<sigma> \<theta> t def x"
      by auto }
  ultimately show "Femto_VHDL_raw.add_to_beh2 \<sigma> (Femto_VHDL_raw.add_to_beh2 \<sigma> \<theta> t def) split def x = Femto_VHDL_raw.add_to_beh2 \<sigma> \<theta> t def x"
    by auto  
qed

lemma split_b_simulate_fin:
  assumes "maxtime, t , \<sigma> , \<gamma>  ,  \<theta>, def \<turnstile> <cs , \<tau>> \<leadsto> res"
  assumes "t \<le> split" and "split \<le> maxtime"
  assumes "\<And>n. n < t \<Longrightarrow> \<tau> n = 0"
  assumes " conc_stmt_wf cs "
  assumes "\<And>n. t < n \<Longrightarrow> \<theta> n = 0"
  shows   "\<exists>res'. split, t, \<sigma>, \<gamma>, \<theta>, def \<turnstile> <cs, \<tau>> \<leadsto> res' \<and> maxtime, split, get_state res', get_event res', get_beh res', def \<turnstile> <cs, get_trans res'> \<leadsto> res"
  using assms
proof (induction rule:b_simulate_fin.inducts)
  case (1 t maxtime \<tau> \<gamma> \<sigma> \<theta> def cs \<tau>' res)
  have hyp1: "\<And>n. n < next_time t \<tau>' \<Longrightarrow> (\<tau>'(next_time t \<tau>' := 0)) n = 0"
    by (simp add: next_time_at_least2)
  have hyp2: "\<And>n. next_time t \<tau>' < n \<Longrightarrow> Femto_VHDL_raw.add_to_beh2 \<sigma> \<theta> t def n = 0"
    by (metis (no_types, lifting) "1.hyps"(3) "1.prems"(3) "1.prems"(4) "1.prems"(5)
    Femto_VHDL_raw.add_to_beh2_def conc_next_time dual_order.strict_trans fun_upd_apply leD
    nat_neq_iff)
  have "t \<le> next_time t \<tau>'"
    using "1.hyps"(3) "1.prems"(3) "1.prems"(4) conc_next_time by blast
  consider (eq_split) "next_time t \<tau>' = split " | (neq_split_less) " next_time t \<tau>' < split" | (neq_split_gt) "next_time t \<tau>' > split"
    by linarith
  thus "\<exists>res'.
             (split, t , \<sigma> , \<gamma> , \<theta>, def \<turnstile> <cs , \<tau>> \<leadsto> res') \<and>
             (maxtime, split , get_state res' , get_event res' , get_beh res', def \<turnstile> <cs , get_trans res'> \<leadsto> res)"
  proof (cases)
    case eq_split
    have "t < next_time t \<tau>' \<or> t = next_time t \<tau>'"
      using \<open>t \<le> next_time t \<tau>'\<close> by auto
    moreover
    { assume "t = next_time t \<tau>'"
      hence "split, t , \<sigma> , \<gamma> , \<theta>, def \<turnstile> <cs , \<tau>> \<leadsto> (split, \<sigma>, \<gamma>, \<theta>, \<tau>)"
        using eq_split  using b_simulate_fin.intros(4) by blast    
      moreover have "maxtime, split , \<sigma> , \<gamma>, \<theta>, def \<turnstile> <cs , \<tau>> \<leadsto> res"
        using \<open>maxtime, next_time t \<tau>' , next_state t \<tau>' \<sigma> , next_event t \<tau>' \<sigma> , Femto_VHDL_raw.add_to_beh2 \<sigma> \<theta> t def, def \<turnstile> <cs , \<tau>' (next_time t \<tau>' := 0)> \<leadsto> res\<close>
        \<open>t , \<sigma> , \<gamma> , \<theta>, def  \<turnstile> <cs , \<tau>> \<longrightarrow>\<^sub>c \<tau>'\<close>
        using \<open>t = next_time t \<tau>'\<close> 
        by (metis "1.hyps"(1) "1.hyps"(2) "1.hyps"(4) b_simulate_fin.intros(1) eq_split)
      ultimately have "\<exists>res'.
       split, t , \<sigma> , \<gamma> , \<theta>, def \<turnstile> <cs , \<tau>> \<leadsto> res' \<and>
       maxtime, split , get_state res' , get_beh' res' , get_beh res', def \<turnstile> <cs , get_trans res'> \<leadsto> res"
        by(intro exI[where x="(split, \<sigma>, \<gamma>, \<theta>, \<tau>)"])(auto) }
    moreover
    { assume "t < next_time t \<tau>'"
      have "split, t, \<sigma>, \<gamma>, \<theta>, def \<turnstile> <cs, \<tau>> \<leadsto> (split, next_state t \<tau>' \<sigma>, next_event t \<tau>' \<sigma>, Femto_VHDL_raw.add_to_beh2 \<sigma> \<theta> t def, \<tau>'(next_time t \<tau>' :=0))"
      proof (rule b_simulate_fin.intros(1))
        show "t < split"
          using \<open>t < next_time t \<tau>'\<close> eq_split by blast
      next
        show "\<not> quiet \<tau> \<gamma>"
          using \<open>\<not> quiet \<tau> \<gamma> \<close> by auto
      next
        show "t , \<sigma> , \<gamma> , \<theta>, def  \<turnstile> <cs , \<tau>> \<longrightarrow>\<^sub>c \<tau>'"
          using \<open>t , \<sigma> , \<gamma> , \<theta>, def  \<turnstile> <cs , \<tau>> \<longrightarrow>\<^sub>c \<tau>'\<close> by auto
      next
        show "next_time t \<tau>' \<le> split"
          using eq_split by auto
      next
        show "split, next_time t \<tau>' , next_state t \<tau>' \<sigma> , next_event t \<tau>' \<sigma> , Femto_VHDL_raw.add_to_beh2 \<sigma> \<theta> t def, def \<turnstile> <cs , \<tau>' (next_time t \<tau>' := 0)> \<leadsto> (split, next_state t \<tau>' \<sigma>, next_event t \<tau>' \<sigma>, Femto_VHDL_raw.add_to_beh2 \<sigma> \<theta> t def, \<tau>'(next_time t \<tau>' := 0))"
          using eq_split  by (simp add: b_simulate_fin.intros(4))
      qed
      moreover have "maxtime, split , next_state t \<tau>' \<sigma> , next_event t \<tau>' \<sigma>, Femto_VHDL_raw.add_to_beh2 \<sigma> \<theta> t def, def \<turnstile> <cs , (\<tau>'(next_time t \<tau>' := 0))> \<leadsto> res"
        using \<open>maxtime, next_time t \<tau>' , next_state t \<tau>' \<sigma> , next_event t \<tau>' \<sigma> , Femto_VHDL_raw.add_to_beh2 \<sigma> \<theta> t def, def \<turnstile> <cs , \<tau>' (next_time t \<tau>' := 0)> \<leadsto> res \<close>
          eq_split by auto
      ultimately have "\<exists>res'.
       split, t , \<sigma> , \<gamma> , \<theta>, def \<turnstile> <cs , \<tau>> \<leadsto> res' \<and>
       maxtime, split , get_state res' , get_beh' res' , get_beh res', def \<turnstile> <cs , get_trans res'> \<leadsto> res"
        by(intro exI[where x="(split, next_state t \<tau>' \<sigma>, next_event t \<tau>' \<sigma>, Femto_VHDL_raw.add_to_beh2 \<sigma> \<theta> t def, \<tau>'(next_time t \<tau>' :=0))"])(auto) }
    ultimately show ?thesis 
      by auto
  next
    case neq_split_gt
    have "t = split \<or> t < split"
      using \<open>t \<le> split\<close> by auto
    moreover
    { assume "t = split"
      hence "split, t, \<sigma>, \<gamma>, \<theta>, def \<turnstile> <cs, \<tau>> \<leadsto> (split, \<sigma>, \<gamma>, \<theta>, \<tau>)"
        by (intro b_simulate_fin.intros(4))
      moreover have "maxtime, split , get_state (split, \<sigma>, \<gamma>, \<theta>, \<tau>) , get_event (split, \<sigma>, \<gamma>, \<theta>, \<tau>) , get_beh (split, \<sigma>, \<gamma>, \<theta>, \<tau>), def \<turnstile> <cs , get_trans (split, \<sigma>, \<gamma>, \<theta>, \<tau>)> \<leadsto> res"
        unfolding `t = split`[THEN sym]
      proof (rule b_simulate_fin.intros(1))
        show "t < maxtime"
          using `t < maxtime` by auto
      next
        show "\<not> quiet (get_trans (t, \<sigma>, \<gamma>, \<theta>, \<tau>)) (get_beh' (t, \<sigma>, \<gamma>, \<theta>, \<tau>))"
          using 1 by auto
      next
        show "t , get_state (t, \<sigma>, \<gamma>, \<theta>, \<tau>) , get_beh' (t, \<sigma>, \<gamma>, \<theta>, \<tau>) , get_beh (t, \<sigma>, \<gamma>, \<theta>, \<tau>), def  \<turnstile> <cs , get_trans (t, \<sigma>, \<gamma>, \<theta>, \<tau>)> \<longrightarrow>\<^sub>c \<tau>'"
          using 1 by auto
      next
        show "next_time t \<tau>' \<le> maxtime"
          using "1.hyps"(4) by blast
      next
        show "maxtime, next_time t
              \<tau>' , next_state t \<tau>'
                    (get_state
                      (t, \<sigma>, \<gamma>, \<theta>, \<tau>)) , next_event t \<tau>' (get_state (t, \<sigma>, \<gamma>, \<theta>, \<tau>)) , Femto_VHDL_raw.add_to_beh2 (get_state (t, \<sigma>, \<gamma>, \<theta>, \<tau>)) (get_beh (t, \<sigma>, \<gamma>, \<theta>, \<tau>)) t def, def \<turnstile> <cs , \<tau>'
    (next_time t \<tau>' := 0)> \<leadsto> res"
          using 1 by auto
      qed
      ultimately have "\<exists>res'.
       split, t , \<sigma> , \<gamma> , \<theta>, def \<turnstile> <cs , \<tau>> \<leadsto> res' \<and>
       maxtime, split , get_state res' , get_beh' res' , get_beh res', def \<turnstile> <cs , get_trans res'> \<leadsto> res"
        using  b_simulate_fin.intros(4) by (intro exI[where x="(split, \<sigma>, \<gamma>, \<theta>, \<tau>)"])(auto) }
    moreover
    { assume "t < split"
      have "split, t , \<sigma> , \<gamma> , \<theta>, def \<turnstile> <cs , \<tau>> \<leadsto> (split, \<sigma>, {}, Femto_VHDL_raw.add_to_beh2 \<sigma> \<theta> t def, \<tau>')"
      proof (intro b_simulate_fin.intros(2))
        show "t < split"
          using \<open>t < split\<close> by auto
      next
        show "\<not> quiet \<tau> \<gamma>"
          using \<open>\<not> quiet \<tau> \<gamma>\<close> by auto
      next
        show " t , \<sigma> , \<gamma> , \<theta>, def  \<turnstile> <cs , \<tau>> \<longrightarrow>\<^sub>c \<tau>'"
          using \<open> t , \<sigma> , \<gamma> , \<theta>, def  \<turnstile> <cs , \<tau>> \<longrightarrow>\<^sub>c \<tau>'\<close> by auto
      next
        show "split < next_time t \<tau>'"
          using neq_split_gt by auto
      qed
      have "split, \<sigma>, {}, Femto_VHDL_raw.add_to_beh2 \<sigma> \<theta> t def, def \<turnstile> <cs, \<tau>'> \<longrightarrow>\<^sub>c \<tau>'"
        by (simp add: b_conc_exec_empty_event)
      have "split < maxtime \<or> split = maxtime"
        using \<open>split \<le> maxtime\<close> by auto
      moreover
      { assume "split = maxtime"
        hence "\<exists>res'.
        split, t , \<sigma> , \<gamma> , \<theta>, def \<turnstile> <cs , \<tau>> \<leadsto> res' \<and>
        maxtime, split , get_state res' , get_beh' res' , get_beh res', def \<turnstile> <cs , get_trans res'> \<leadsto> res"
        proof -
          have "next_time t \<tau>' < maxtime"
            using \<open>maxtime, next_time t \<tau>' , next_state t \<tau>' \<sigma> , next_event t \<tau>' \<sigma> , Femto_VHDL_raw.add_to_beh2 \<sigma> \<theta> t def, def \<turnstile> <cs , \<tau>' (next_time t \<tau>' := 0)> \<leadsto> res\<close> \<open>split = maxtime\<close> bau neq_split_gt by blast
          then show ?thesis
            using \<open>split = maxtime\<close> neq_split_gt by linarith
        qed }
      moreover 
      { assume "split < maxtime"
        have " maxtime, split , \<sigma> , {} , Femto_VHDL_raw.add_to_beh2 \<sigma> \<theta> t def, def \<turnstile> <cs ,  \<tau>'> \<leadsto> res"
        proof (rule b_simulate_fin.intros(1))
          show "split < maxtime"
            using \<open>split < maxtime\<close> by auto
        next
          show "\<not> quiet \<tau>' {}"
            by (metis Suc_eq_plus1 Suc_leI \<open>t < split\<close> leD neq_split_gt next_time_def quiet_def)
        next
          show " split , \<sigma> , {} , Femto_VHDL_raw.add_to_beh2 \<sigma> \<theta> t def, def  \<turnstile> <cs , \<tau>'> \<longrightarrow>\<^sub>c \<tau>'"
            by (simp add: \<open>split , \<sigma> , {} , Femto_VHDL_raw.add_to_beh2 \<sigma> \<theta> t def, def \<turnstile> <cs , \<tau>'> \<longrightarrow>\<^sub>c \<tau>'\<close>)
        next
          show "next_time split \<tau>' \<le> maxtime"
          proof -
            have "next_time t \<tau>' = maxtime \<or> next_time t \<tau>' < maxtime"
              using \<open>maxtime, next_time t \<tau>' , next_state t \<tau>' \<sigma> , next_event t \<tau>' \<sigma> , Femto_VHDL_raw.add_to_beh2 \<sigma> \<theta> t def, def \<turnstile> <cs , \<tau>' (next_time t \<tau>' := 0)> \<leadsto> res\<close> bau by blast
            then show ?thesis
              by (metis (no_types) Suc_eq_plus1 \<open>split < maxtime\<close> nat_less_le next_time_def not_le not_less_eq_eq)
          qed
        next
          have "next_time split \<tau>' = next_time t \<tau>'"
            by (metis Suc_eq_plus1 \<open>t < split\<close> less_Suc_eq_le neq_split_gt next_time_def not_le)
          have " next_state split \<tau>' \<sigma> =  next_state t \<tau>' \<sigma>"
            by (simp add: \<open>next_time split \<tau>' = next_time t \<tau>'\<close> next_state_def)
          have "next_event split \<tau>' \<sigma> = next_event t \<tau>' \<sigma>"
            by (simp add: \<open>next_time split \<tau>' = next_time t \<tau>'\<close> next_event_def)
          have "\<And>s. \<forall>n>t. \<theta> n s = 0"
            using 1  by (simp add: zero_fun_def)
          hence "Femto_VHDL_raw.add_to_beh2 \<sigma> (Femto_VHDL_raw.add_to_beh2 \<sigma> \<theta> t def) split def = Femto_VHDL_raw.add_to_beh2 \<sigma> \<theta> t def"
            using \<open>t < split\<close> add_to_beh2_fixed_point by blast
          show "maxtime, next_time split \<tau>' , next_state split \<tau>' \<sigma> , next_event split \<tau>' \<sigma> , Femto_VHDL_raw.add_to_beh2 \<sigma> (Femto_VHDL_raw.add_to_beh2 \<sigma> \<theta> t def) split def, def \<turnstile> <cs , \<tau>' (next_time split \<tau>' := 0)> \<leadsto> res"          
            using \<open>maxtime, next_time t \<tau>' , next_state t \<tau>' \<sigma> , next_event t \<tau>' \<sigma> , Femto_VHDL_raw.add_to_beh2 \<sigma> \<theta> t def, def \<turnstile> <cs , \<tau>' (next_time t \<tau>' := 0)> \<leadsto> res\<close>
            by (simp add: \<open>Femto_VHDL_raw.add_to_beh2 \<sigma> (Femto_VHDL_raw.add_to_beh2 \<sigma> \<theta> t def) split def = Femto_VHDL_raw.add_to_beh2 \<sigma> \<theta> t def\<close> \<open>next_time split \<tau>' = next_time t \<tau>'\<close> next_event_alt_def next_state_def)
        qed
        hence "\<exists>res'.
          split, t , \<sigma> , \<gamma> , \<theta>, def \<turnstile> <cs , \<tau>> \<leadsto> res' \<and>
          maxtime, split , get_state res' , get_beh' res' , get_beh res', def \<turnstile> <cs , get_trans res'> \<leadsto> res"
          using \<open>split, t , \<sigma> , \<gamma> , \<theta>, def \<turnstile> <cs , \<tau>> \<leadsto> (split, \<sigma>, {}, Femto_VHDL_raw.add_to_beh2 \<sigma> \<theta> t def, \<tau>')\<close>
          by (intro exI[where x="(split, \<sigma>, {}, Femto_VHDL_raw.add_to_beh2 \<sigma> \<theta> t def, \<tau>')"]) auto }
      ultimately have ?thesis
        by auto }
    ultimately show ?thesis 
      by auto
  next
    case neq_split_less
    then obtain res' where  "split, next_time t \<tau>' , next_state t \<tau>' \<sigma> , next_event t \<tau>' \<sigma> , Femto_VHDL_raw.add_to_beh2 \<sigma> \<theta> t def, def \<turnstile> <cs , \<tau>'(next_time t \<tau>' := 0)> \<leadsto> res'" 
      and  "maxtime, split , get_state res' , get_beh' res' , get_beh res', def \<turnstile> <cs , get_trans res'> \<leadsto> res"
      using  1(6)[OF _ `split \<le> maxtime` hyp1 `conc_stmt_wf cs` hyp2]  using dual_order.order_iff_strict by blast
    have "split, t , \<sigma> , \<gamma> , \<theta>, def \<turnstile> <cs , \<tau>> \<leadsto> res'"
    proof (rule b_simulate_fin.intros(1))
      show "t < split"
        using \<open>t \<le> next_time t \<tau>'\<close> dual_order.strict_trans2 neq_split_less by blast
    next
      show "\<not> quiet \<tau> \<gamma>"
        by (simp add: "1.hyps"(2))
    next
      show "t , \<sigma> , \<gamma> , \<theta>, def  \<turnstile> <cs , \<tau>> \<longrightarrow>\<^sub>c \<tau>'"
        using "1.hyps"(3) by blast
    next
      show "next_time t \<tau>' \<le> split"
        using nat_less_le neq_split_less by blast
    next
      show "split, next_time t \<tau>' , next_state t \<tau>' \<sigma> , next_event t \<tau>' \<sigma> , Femto_VHDL_raw.add_to_beh2 \<sigma> \<theta> t def, def \<turnstile> <cs , \<tau>'(next_time t \<tau>' := 0)> \<leadsto> res'"
        using \<open>split, next_time t \<tau>' , next_state t \<tau>' \<sigma> , next_event t \<tau>' \<sigma> , Femto_VHDL_raw.add_to_beh2 \<sigma> \<theta> t def, def \<turnstile> <cs , \<tau>' (next_time t \<tau>' := 0)> \<leadsto> res'\<close> by blast
    qed
    thus ?thesis
      using \<open>maxtime, split , get_state res' , get_beh' res' , get_beh res', def \<turnstile> <cs , get_trans res'> \<leadsto> res\<close> by blast
  qed
next
  case (2 t maxtime \<tau> \<gamma> \<sigma> \<theta> def cs \<tau>')
  then consider (eq) "t = split" | (neq) "t < split"
    by linarith
  then show ?case 
  proof (cases)
    case eq
    then show ?thesis 
      using "2.hyps"(1) "2.hyps"(2) "2.hyps"(3) "2.hyps"(4) b_simulate_fin.intros(2) b_simulate_fin.intros(4) by fastforce
  next
    case neq
    have *: "split, t , \<sigma> , \<gamma> , \<theta>, def \<turnstile> <cs , \<tau>> \<leadsto> (split, \<sigma>, {}, Femto_VHDL_raw.add_to_beh2 \<sigma> \<theta> t def, \<tau>')"
    proof (rule b_simulate_fin.intros(2))
      show "t < split"
        using neq by auto
    next
      show "\<not> quiet \<tau> \<gamma>"
        using 2 by auto
    next
      show "t , \<sigma> , \<gamma> , \<theta>, def  \<turnstile> <cs , \<tau>> \<longrightarrow>\<^sub>c \<tau>'"
        using 2 by auto
    next
      show "split < next_time t \<tau>'"
        using 2  by linarith
    qed
    have "split < maxtime \<or> split = maxtime"
      using 2 by linarith
    moreover
    { assume "split = maxtime"
      hence "maxtime, split , \<sigma>, {} , Femto_VHDL_raw.add_to_beh2 \<sigma> \<theta> t def, def \<turnstile> <cs , \<tau>'> \<leadsto> (maxtime, \<sigma>, {}, Femto_VHDL_raw.add_to_beh2 \<sigma> (Femto_VHDL_raw.add_to_beh2 \<sigma> \<theta> t def) split def, \<tau>')"
        by (smt "2.prems"(5) add_to_beh2_fixed_point b_simulate_fin.simps neq zero_fun_def) }
    moreover
    { assume "split < maxtime" 
      have "maxtime, split , \<sigma>, {} , Femto_VHDL_raw.add_to_beh2 \<sigma> \<theta> t def, def \<turnstile> <cs , \<tau>'> \<leadsto> (maxtime, \<sigma>, {}, Femto_VHDL_raw.add_to_beh2 \<sigma> (Femto_VHDL_raw.add_to_beh2 \<sigma> \<theta> t def) split def, \<tau>')"
      proof (rule b_simulate_fin.intros(2))
        show "split < maxtime"
          using `split < maxtime` by auto
      next
        show "\<not> quiet \<tau>' {}"
          by (metis "2.hyps"(1) "2.hyps"(4) One_nat_def add.right_neutral add_Suc_right leD less_Suc_eq_le next_time_def quiet_def)
      next
        show "split , \<sigma> , {} , Femto_VHDL_raw.add_to_beh2 \<sigma> \<theta> t def, def  \<turnstile> <cs , \<tau>'> \<longrightarrow>\<^sub>c \<tau>'"
          by (simp add: b_conc_exec_empty_event)
      next
        show "maxtime < next_time split \<tau>'"
          by (metis "2.hyps"(1) "2.hyps"(4) Suc_eq_plus1 Suc_le_eq leD next_time_def)
      qed }
    ultimately have "maxtime, split , \<sigma>, {} , Femto_VHDL_raw.add_to_beh2 \<sigma> \<theta> t def, def \<turnstile> <cs , \<tau>'> \<leadsto> (maxtime, \<sigma>, {}, Femto_VHDL_raw.add_to_beh2 \<sigma> (Femto_VHDL_raw.add_to_beh2 \<sigma> \<theta> t def) split def, \<tau>')"
      by auto
    hence "maxtime, split , \<sigma>, {} , Femto_VHDL_raw.add_to_beh2 \<sigma> \<theta> t def, def \<turnstile> <cs , \<tau>'> \<leadsto> (maxtime, \<sigma>, {}, Femto_VHDL_raw.add_to_beh2 \<sigma> \<theta> t def, \<tau>')"
      using add_to_beh2_fixed_point 
      by (simp add: add_to_beh2_fixed_point "2.prems"(5) neq zero_fun_def)
    thus ?thesis 
      apply (intro exI[where x="(split, \<sigma>, {}, Femto_VHDL_raw.add_to_beh2 \<sigma> \<theta> t def, \<tau>')"])
      using * by auto
  qed
next
  case (3 t maxtime \<tau> \<gamma> \<sigma> \<theta> def cs)
  hence "t < split \<or> t = split"
    by auto
  moreover
  { assume "t = split"
    hence ?case
      using 3  using b_simulate_fin.intros(3) b_simulate_fin.intros(4) by fastforce }
  moreover
  { assume "t < split"
    hence " split, t , \<sigma> , \<gamma> , \<theta>, def \<turnstile> <cs , \<tau>> \<leadsto> (split, \<sigma>, \<gamma>, \<theta>, 0)"
      using 3 apply (intro b_simulate_fin.intros(3))
      by auto
    moreover have "maxtime, split , \<sigma> , \<gamma> , \<theta>, def \<turnstile> <cs , 0> \<leadsto> (maxtime, \<sigma>, \<gamma>, \<theta>, 0)"
    proof (cases "split = maxtime")
      case True
      then show ?thesis 
        by (simp add: b_simulate_fin.intros(4))
    next
      case False
      then show ?thesis 
        by (metis (full_types) "3.hyps"(2) "3.prems"(2) b_simulate_fin.intros(3) dual_order.order_iff_strict quiet_def)
    qed
    ultimately have  ?case
      by (auto intro!: exI) }
  ultimately show ?case 
    by auto
next
  case (4 t maxtime \<sigma> \<gamma> \<theta> def cs \<tau>)
  hence "split, t , \<sigma> , \<gamma> , \<theta>, def \<turnstile> <cs , \<tau>> \<leadsto> (split, \<sigma>, \<gamma>, \<theta>, \<tau>)"
    by (auto intro!: b_simulate_fin.intros(4))
  moreover have "maxtime, split , \<sigma> , \<gamma> , \<theta>, def \<turnstile> <cs , \<tau>> \<leadsto> (maxtime, \<sigma>, \<gamma>, \<theta>, \<tau>)"
    using 4 by (auto intro!: b_simulate_fin.intros(4))
  ultimately show ?case 
    by (auto intro!: exI)
qed

lemma case_quiesce2:
  assumes "t < maxtime"
  assumes "quiet \<tau> \<gamma>"
  assumes "(maxtime, t, \<sigma>, \<gamma>, \<theta>, def \<turnstile> <cs, \<tau>> \<leadsto> res)"
  shows "get_time res = maxtime \<and> get_beh res = \<theta> \<and> get_state res = \<sigma> \<and> get_trans res = 0"
  apply(rule bau[OF assms(3)])
  using assms by auto

lemma pseudo_inductive_rule_b_simulate_fin:
  assumes "split, t, \<sigma>, \<gamma>, \<theta>, def \<turnstile> <cs, \<tau>> \<leadsto> res'"
  assumes "maxtime, split, get_state res', get_event res', get_beh res', def \<turnstile> <cs, get_trans res'> \<leadsto> res"
  assumes "\<forall>n < t. \<tau> n = 0" and "\<forall>n > t. \<theta> n = 0"
  shows   "maxtime, t, \<sigma>, \<gamma>, \<theta>, def \<turnstile> <cs, \<tau>> \<leadsto> res"
  using assms
proof (induction arbitrary: maxtime rule: b_simulate_fin.inducts)
  case (1 t maxtime' \<tau> \<gamma> \<sigma> \<theta> def cs \<tau>' res')
  hence "t \<le> next_time t \<tau>'"
    by (meson b_conc_exec_preserve_trans_removal next_time_at_least)
  hence atb: "\<forall>n>next_time t \<tau>'. Femto_VHDL_raw.add_to_beh2 \<sigma> \<theta> t def n = 0"
    using 1 by (simp add: Femto_VHDL_raw.add_to_beh2_def)
  have trans: " \<forall>n<next_time t \<tau>'. (\<tau>'(next_time t \<tau>' := 0)) n = 0"
    by (simp add: next_time_at_least2)
  have IH: "maxtime, next_time t \<tau>' , next_state t \<tau>' \<sigma> , next_event t \<tau>' \<sigma> , Femto_VHDL_raw.add_to_beh2 \<sigma> \<theta> t def, def \<turnstile> <cs , \<tau>'
    (next_time t \<tau>' := 0)> \<leadsto> res"
    using 1(6)[OF 1(7) trans atb] by metis
  have "maxtime' \<le> maxtime"
    using 1(7) by (induction)(auto)
  show ?case 
    apply (rule b_simulate_fin.intros(1))
    using 1 \<open>maxtime' \<le> maxtime\<close> apply linarith
    using 1  apply linarith
    using 1(3) apply simp
    using 1 \<open>maxtime' \<le> maxtime\<close> apply simp
    using IH by simp
next
  case (2 t split \<tau> \<gamma> \<sigma> \<theta> def cs \<tau>')
  hence *: "maxtime, split , \<sigma> , {}, Femto_VHDL_raw.add_to_beh2 \<sigma> \<theta> t def, def \<turnstile> <cs , \<tau>'> \<leadsto> res"
    by auto
  hence "split \<le> maxtime"
    by (induction)(auto)
  hence "split = maxtime \<or> split < maxtime"
    by auto
  moreover
  { assume "split = maxtime"
    hence ?case
      by (metis "2.hyps"(1) "2.hyps"(2) "2.hyps"(3) "2.hyps"(4) \<open>maxtime, split , \<sigma> , {} , Femto_VHDL_raw.add_to_beh2 \<sigma> \<theta> t def, def \<turnstile> <cs , \<tau>'> \<leadsto> res\<close> b_simulate_fin.intros(2) b_simulate_fin.intros(4) b_simulate_fin_deterministic)  }
  moreover
  { assume "split < maxtime"
    have "\<not> quiet \<tau>' {}"
      using 2  by (metis (full_types) Suc_eq_plus1 less_Suc_eq_le next_time_def not_le quiet_def)
    have "split, \<sigma>, {}, Femto_VHDL_raw.add_to_beh2 \<sigma> \<theta> t def, def \<turnstile> <cs, \<tau>'> \<longrightarrow>\<^sub>c \<tau>'"
      by (simp add: b_conc_exec_empty_event)
    have "next_time split \<tau>' = next_time t \<tau>'"
      by (metis \<open>\<not> quiet \<tau>' {}\<close> next_time_def quiet_def)
    have "maxtime < next_time split \<tau>' \<or> next_time split \<tau>' \<le> maxtime"
      by auto
    moreover
    { assume "maxtime < next_time split \<tau>'"
      hence "res = (maxtime, \<sigma>, {}, Femto_VHDL_raw.add_to_beh2 \<sigma> (Femto_VHDL_raw.add_to_beh2 \<sigma> \<theta> t def) split def, \<tau>')"
        using bau[OF *] 
        by (smt \<open>\<not> quiet \<tau>' {}\<close> \<open>split , \<sigma> , {} , Femto_VHDL_raw.add_to_beh2 \<sigma> \<theta> t def, def \<turnstile> <cs , \<tau>'> \<longrightarrow>\<^sub>c \<tau>'\<close> \<open>split < maxtime\<close> b_conc_exec_deterministic nat_less_le not_less)
      moreover have "maxtime, t , \<sigma> , \<gamma> , \<theta>, def \<turnstile> <cs , \<tau>> \<leadsto>(maxtime, \<sigma>, {}, Femto_VHDL_raw.add_to_beh2 \<sigma> \<theta> t def, \<tau>')"
        by (metis (no_types, lifting) "2.hyps"(1) "2.hyps"(2) "2.hyps"(3) \<open>maxtime < next_time split \<tau>'\<close> \<open>next_time split \<tau>' = next_time t \<tau>'\<close> \<open>split < maxtime\<close> b_simulate_fin.intros(2) dual_order.strict_trans)
      moreover have "Femto_VHDL_raw.add_to_beh2 \<sigma> (Femto_VHDL_raw.add_to_beh2 \<sigma> \<theta> t def) split def = Femto_VHDL_raw.add_to_beh2 \<sigma> \<theta> t def"
        by (simp add: "2.hyps"(1) "2.prems"(3) add_to_beh2_fixed_point zero_fun_def)
      ultimately have ?case
        by auto }
    moreover
    { assume "next_time split \<tau>' \<le> maxtime"
      moreover have "next_state split \<tau>' \<sigma> = next_state t \<tau>' \<sigma>"
        by (simp add: \<open>next_time split \<tau>' = next_time t \<tau>'\<close> next_state_def)
      moreover have "next_event t \<tau>' \<sigma> = next_event split \<tau>' \<sigma>"
        by (simp add: \<open>next_time split \<tau>' = next_time t \<tau>'\<close> next_event_alt_def next_state_def)
      moreover have "Femto_VHDL_raw.add_to_beh2 \<sigma> (Femto_VHDL_raw.add_to_beh2 \<sigma> \<theta> t def) split def = Femto_VHDL_raw.add_to_beh2 \<sigma> \<theta> t def"
        by (simp add: "2.hyps"(1) "2.prems"(3) add_to_beh2_fixed_point zero_fun_def)
      ultimately have ?case
        by (smt "*" "2.hyps"(1) "2.hyps"(2) "2.hyps"(3) \<open>\<not> quiet \<tau>' {}\<close> \<open>next_time split \<tau>' =
        next_time t \<tau>'\<close> \<open>split , \<sigma> , {} , Femto_VHDL_raw.add_to_beh2 \<sigma> \<theta> t def, def \<turnstile> <cs , \<tau>'> \<longrightarrow>\<^sub>c
        \<tau>'\<close> \<open>split < maxtime\<close> b_simulate_fin.intros(1) case_bau dual_order.strict_trans) }
    ultimately have ?case
      by auto }
  ultimately show ?case
    by auto
next
  case (3 t split \<tau> \<gamma> \<sigma> \<theta> def cs)
  have "split \<le> maxtime"
    using 3(3) by (induction)(auto)
  hence "split = maxtime \<or> split < maxtime"
    by auto
  moreover
  { assume "split = maxtime"
    hence "res = (maxtime, \<sigma>, \<gamma>, \<theta>, 0)"
      using 3 
      by (metis (no_types, hide_lams) Collect_mem_eq b_simulate_fin.intros(4) b_simulate_fin_deterministic comp_apply fst_conv snd_conv) }
  moreover
  { assume "split < maxtime"
    have "res = (maxtime, \<sigma>, \<gamma>, \<theta>, 0)"
      using case_quiesce2[OF `split < maxtime` 3(2)] 3(3) 
      by (metis "3.hyps"(2) Pair_inject \<open>split < maxtime\<close> b_simulate_fin.intros(3) b_simulate_fin_deterministic comp_apply comp_def fst_conv old.prod.exhaust quiet_def snd_conv) }
  ultimately have res_def: "res = (maxtime, \<sigma>, \<gamma>, \<theta>, 0)"
    by auto
  show ?case
    unfolding res_def
    apply (intro b_simulate_fin.intros(3))
    using "3.hyps"(1) \<open>split \<le> maxtime\<close> order.strict_trans2 apply blast
    using "3.hyps"(2) by auto
next
  case (4 t split \<sigma> \<gamma> \<theta> def cs \<tau>)
  then show ?case by auto
qed

lemma conc_stmt_wf_nand4:
  "conc_stmt_wf nand4"
  unfolding conc_stmt_wf_def nand4_def by auto

lemma get_trans_res_suc_maxtime:
  assumes "maxtime, t, \<sigma>, \<gamma>, \<theta>, def \<turnstile> <cs, \<tau>> \<leadsto> res"
  assumes "sig \<notin> set (signals_from cs)"
  shows   "get_trans res (maxtime + 1) sig = \<tau> (maxtime + 1) sig"
  using assms
proof (induction )
  case (1 t maxtime \<tau> \<gamma> \<sigma> \<theta> def cs \<tau>' res)
  hence "get_trans res (maxtime + 1) sig = (\<tau>'(next_time t \<tau>' := 0)) (maxtime + 1) sig "
    by auto
  then show ?case 
    using b_conc_exec_modifies_local[OF 1(3) 1(7)] 
    by (metis "1.hyps"(1) "1.hyps"(4) Suc_eq_plus1 fun_upd_other le_add1 le_trans less_imp_le_nat not_less_eq_eq)
next
  case (2 t maxtime \<tau> \<gamma> \<sigma> \<theta> def cs \<tau>')
  hence "get_trans (maxtime, \<sigma>, {}, Femto_VHDL_raw.add_to_beh2 \<sigma> \<theta> t def, \<tau>') maxtime sig = \<tau>' maxtime sig"
    by auto
  then show ?case 
    using b_conc_exec_modifies_local[OF 2(3) 2(5)]
    using "2.hyps"(1) by auto
next
  case (3 t maxtime \<tau> \<gamma> \<sigma> \<theta> def cs)
  then show ?case by (metis comp_apply quiet_def snd_conv)
next
  case (4 t maxtime \<sigma> \<gamma> \<theta> def cs \<tau>)
  then show ?case by auto
qed

lemma get_trans_res_maxtime:
  assumes "maxtime, t, \<sigma>, \<gamma>, \<theta>, def \<turnstile> <cs, \<tau>> \<leadsto> res"
  assumes "\<tau> t = 0"
  shows   "get_trans res maxtime = 0"
  using assms
proof (induction )
  case (1 t maxtime \<tau> \<gamma> \<sigma> \<theta> def cs \<tau>' res)
  hence "get_trans res maxtime = 0"
    by auto
  then show ?case 
    by (metis "1.hyps"(1) dual_order.strict_implies_order fun_upd_apply zero_fun_def)
next
  case (2 t maxtime \<tau> \<gamma> \<sigma> \<theta> def cs \<tau>')
  hence "get_trans (maxtime, \<sigma>, {}, Femto_VHDL_raw.add_to_beh2 \<sigma> \<theta> t def, \<tau>') maxtime  = \<tau>' maxtime"
    by auto
  then show ?case 
    using "2.hyps"(1)  by (smt "2.hyps"(4) next_time_at_least2 zero_fun_def)
next
  case (3 t maxtime \<tau> \<gamma> \<sigma> \<theta> def cs)
  then show ?case  by (simp add: zero_fun_def)
next
  case (4 t maxtime \<sigma> \<gamma> \<theta> def cs \<tau>)
  then show ?case  by (simp add: zero_fun_def)
qed

lemma b_simulate_fin_preserve_trans_removal:
  assumes "maxtime, t, \<sigma>, \<gamma>, \<theta>, def \<turnstile> <cs, \<tau>> \<leadsto> res"
  assumes "\<And>n. n < t \<Longrightarrow>  \<tau> n = 0"
  shows   "\<And>n. n < maxtime \<Longrightarrow>  get_trans res n = 0"
  using assms
proof (induction )
  case (1 t maxtime \<tau> \<gamma> \<sigma> \<theta> def cs \<tau>' res)
  hence "\<And>n. n < next_time t \<tau>' \<Longrightarrow> (\<tau>'(next_time t \<tau>' := 0)) n = 0"
    by (simp add: next_time_at_least2)
  hence IH: "\<And>n. n < maxtime \<Longrightarrow> get_trans res n = 0"
    using 1 by blast
  then show ?case 
    using 1 by auto
next
  case (2 t maxtime \<tau> \<gamma> \<sigma> \<theta> def cs \<tau>')
  then show ?case 
    using b_conc_exec_preserve_trans_removal 
    by (metis comp_apply dual_order.strict_trans2 less_imp_le_nat next_time_at_least2 snd_conv)
next
  case (3 t maxtime \<tau> \<gamma> \<sigma> \<theta> def cs)
  then show ?case 
    by (simp add: zero_fun_def)
next
  case (4 t maxtime \<sigma> \<gamma> \<theta> def cs \<tau>)
  then show ?case by auto
qed

lemma add_to_beh2_preserves_hist:
  assumes "\<And>n. n > t \<Longrightarrow> \<theta> n = 0"
  shows "\<And>n. n > t \<Longrightarrow> Femto_VHDL_raw.add_to_beh2 \<sigma> \<theta> t def n = 0"
  using assms
  by (simp add: Femto_VHDL_raw.add_to_beh2_def)

lemma b_simulate_fin_preserves_hist:
  assumes "maxtime, t, \<sigma>, \<gamma>, \<theta>, def \<turnstile> <cs, \<tau>> \<leadsto> res"
  assumes "\<And>n. n > t \<Longrightarrow>  \<theta> n = 0"
  assumes "\<And>n. n < t \<Longrightarrow> \<tau> n = 0"
  shows   "\<And>n. n > maxtime \<Longrightarrow>  get_beh res n = 0"
  using assms
proof (induction)
  case (1 t maxtime \<tau> \<gamma> \<sigma> \<theta> def cs \<tau>' res)
  hence "t \<le> next_time t \<tau>'"
    by (meson b_conc_exec_preserve_trans_removal next_time_at_least)
  hence "\<And>n. next_time t \<tau>' < n \<Longrightarrow> Femto_VHDL_raw.add_to_beh2 \<sigma> \<theta> t def n = 0"
    using add_to_beh2_preserves_hist 1  by (metis le_less_trans)
  moreover have "\<And>n. n < next_time t \<tau>' \<Longrightarrow> (\<tau>'(next_time t \<tau>' := 0)) n = 0"
    using 1  by (simp add: next_time_at_least2)
  ultimately show ?case 
    using 1 by blast
next
  case (2 t maxtime \<tau> \<gamma> \<sigma> \<theta> def cs \<tau>')
  then show ?case 
    using add_to_beh2_preserves_hist 
    by (metis comp_apply dual_order.strict_trans fst_conv snd_conv)
next
  case (3 t maxtime \<tau> \<gamma> \<sigma> \<theta> def cs)
  then show ?case by auto
next
  case (4 t maxtime \<sigma> \<gamma> \<theta> def cs \<tau>)
  then show ?case by auto
qed


lemma b_simulate_fin_preserves_zeroed_unmodified_sigs:
  assumes "maxtime, t, \<sigma>, \<gamma>, \<theta>, def \<turnstile> <cs, \<tau>> \<leadsto> res"
  assumes "sig \<notin> set (signals_from cs)"
  assumes "\<tau> t sig = 0"
  shows   "get_trans res maxtime sig = 0"
  using assms
proof (induction)
  case (1 t maxtime \<tau> \<gamma> \<sigma> \<theta> def cs \<tau>' res)
  then show ?case 
    by (simp add: zero_fun_def)
next
  case (2 t maxtime \<tau> \<gamma> \<sigma> \<theta> def cs \<tau>')
  then show ?case 
    by (metis comp_apply snd_conv until_next_time_zero zero_fun_def)
next
  case (3 t maxtime \<tau> \<gamma> \<sigma> \<theta> def cs)
  then show ?case  by (simp add: zero_fun_def)
next
  case (4 t maxtime \<sigma> \<gamma> \<theta> def cs \<tau>)
  then show ?case by auto
qed

lemma get_state_b_simulate_fin:
  assumes "maxtime, t , \<sigma> , \<gamma> , \<theta>, def \<turnstile> <cs , \<tau>> \<leadsto> res"
  assumes "sig \<notin> set (signals_from cs)"
  assumes "\<tau> maxtime sig \<noteq> 0"
  assumes "t < maxtime"
  shows   "get_state res sig = the (\<tau> maxtime sig)"
  using assms
proof (induction)
  case (1 t maxtime \<tau> \<gamma> \<sigma> \<theta> def cs \<tau>' res)
  hence "next_time t \<tau>' < maxtime \<or> next_time t \<tau>' = maxtime"
    by auto
  moreover
  { assume "next_time t \<tau>' < maxtime"
    hence ?case
      using 1  using b_conc_exec_modifies_local_strongest by fastforce }
  moreover
  { assume "next_time t \<tau>' = maxtime"
    hence *: "maxtime, maxtime , next_state t \<tau>' \<sigma> , next_event t \<tau>' \<sigma> , Femto_VHDL_raw.add_to_beh2 \<sigma> \<theta> t def, def \<turnstile> <cs , \<tau>'(next_time t \<tau>' := 0)> \<leadsto> res"
      using 1 by auto
    have "res = (maxtime, next_state t \<tau>' \<sigma>, next_event t \<tau>' \<sigma>, Femto_VHDL_raw.add_to_beh2 \<sigma> \<theta> t def, \<tau>'(next_time t \<tau>' := 0))"
      using bau[OF *] by blast
    hence "get_state res = next_state t \<tau>' \<sigma>"
      by auto
    hence ?case
      using 1 
      by (metis (mono_tags, hide_lams) \<open>next_time t \<tau>' = maxtime\<close> b_conc_exec_modifies_local_strongest comp_apply domIff next_state_def override_on_apply_in zero_option_def) }
  ultimately show ?case 
    by auto
next
  case (2 t maxtime \<tau> \<gamma> \<sigma> \<theta> def cs \<tau>')
  then show ?case 
    by (metis b_conc_exec_modifies_local_strongest until_next_time_zero zero_fun_def)
next
  case (3 t maxtime \<tau> \<gamma> \<sigma> \<theta> def cs)
  then show ?case  by (metis quiet_def zero_fun_def)
next
  case (4 t maxtime \<sigma> \<gamma> \<theta> def cs \<tau>)
  then show ?case by auto
qed

lemma get_state_b_simulate_fin_inf_none:
  assumes "maxtime, t , \<sigma> , \<gamma> , \<theta>, def \<turnstile> <cs , \<tau>> \<leadsto> res"
  assumes "sig \<notin> set (signals_from cs)"
  assumes "inf_time (to_trans_raw_sig \<tau>) sig maxtime = None"
  shows   "get_state res sig = \<sigma> sig"
  using assms
proof (induction)
  case (1 t maxtime \<tau> \<gamma> \<sigma> \<theta> def cs \<tau>' res)
  have "inf_time (to_trans_raw_sig (\<tau>'(next_time t \<tau>' := 0))) sig maxtime = None"
    unfolding inf_time_none_iff[THEN sym]
  proof 
    { fix x 
      assume " x \<in> dom (to_trans_raw_sig (\<tau>'(next_time t \<tau>' := 0)) sig)"
      hence "(\<tau>' (next_time t \<tau>' := 0)) x sig \<noteq> None"
        unfolding to_trans_raw_sig_def dom_def by auto
      hence "x \<noteq> next_time t \<tau>'"
        by (metis fun_upd_def zero_fun_def zero_option_def)
      assume " x \<le> maxtime"
      have "(\<tau>'(next_time t \<tau>' := 0)) x sig = \<tau>' x sig"
        using `x \<noteq> next_time t \<tau>'` by auto
      also have "... = \<tau> x sig"
        using "1.hyps"(3) "1.prems"(1) b_conc_exec_modifies_local_strongest by fastforce
      also have "... = None"
        using 1(8) `x \<le> maxtime` unfolding inf_time_none_iff[THEN sym]
          to_trans_raw_sig_def dom_def by auto
      finally have False
        using \<open>(\<tau>' (next_time t \<tau>' := 0)) x sig \<noteq> None\<close> by auto }
    thus "\<And>x. x \<in> dom (to_trans_raw_sig (\<tau>'(next_time t \<tau>' := 0)) sig) \<Longrightarrow> maxtime < x"
      using le_less_linear by blast
  qed
  hence "get_state res sig = next_state t \<tau>' \<sigma> sig"
    using "1.IH" "1.prems"(1) by blast
  moreover have "sig \<notin> (dom (\<tau>' (next_time t \<tau>'))) "
    using 1(8) `next_time t \<tau>' \<le> maxtime`
    using "1.hyps"(3) "1.prems"(1) b_conc_exec_modifies_local_strongest 
    by (metis domIff inf_time_noneE2 to_trans_raw_sig_def zero_option_def)
  ultimately have "next_state t \<tau>' \<sigma> sig = \<sigma> sig"
    unfolding next_state_def Let_def by auto
  then show ?case 
    using \<open>get_state res sig = next_state t \<tau>' \<sigma> sig\<close> by auto    
next
  case (2 t maxtime \<tau> \<gamma> \<sigma> \<theta> def cs \<tau>')
  then show ?case 
    by auto
next
  case (3 t maxtime \<tau> \<gamma> \<sigma> \<theta> def cs)
  then show ?case 
    by auto
next
  case (4 t maxtime \<sigma> \<gamma> \<theta> def cs \<tau>)
  then show ?case by auto
qed



lemma get_state_b_simulate_fin_signal_of:
  assumes "maxtime, t , \<sigma> , \<gamma> , \<theta>, def \<turnstile> <cs , \<tau>> \<leadsto> res"
  assumes "sig \<notin> set (signals_from cs)"
  assumes "t < maxtime"
  assumes "\<And>n. n < t \<Longrightarrow> \<tau> n = 0"
  shows   "get_state res sig = signal_of (\<sigma> sig) \<tau> sig maxtime"
  using assms
proof (induction)
  case (1 t maxtime \<tau> \<gamma> \<sigma> \<theta> def cs \<tau>' res)
  hence "next_time t \<tau>' < maxtime \<or> next_time t \<tau>' = maxtime"
    by auto
  moreover
  { assume "next_time t \<tau>' < maxtime"
    hence IH: "get_state res sig = signal_of (next_state t \<tau>' \<sigma> sig) (\<tau>'(next_time t \<tau>' := 0)) sig maxtime"
      using 1 next_time_at_least2 by fastforce
    also have "... = signal_of (next_state t \<tau>' \<sigma> sig) \<tau>' sig maxtime"
      apply (rule signal_of_rem_curr_trans_at_t[where \<sigma>="next_state t \<tau>' \<sigma>" and A="sig"])
       apply (metis comp_eq_dest_lhs next_state_def override_on_apply_in)
      by (simp add: next_time_at_least2)
    finally have ?case
      using b_conc_exec_does_not_modify_signals2[OF _ 1(3) 1(7) 1(4)]
      by (simp add: "1.prems"(3)) }
  moreover
  { assume "next_time t \<tau>' = maxtime"
    hence "res = (maxtime, next_state t \<tau>' \<sigma>, next_event t \<tau>' \<sigma>, Femto_VHDL_raw.add_to_beh2 \<sigma> \<theta> t def, \<tau>'(next_time t \<tau>' := 0))"
      using bau[OF 1(5)] by auto
    hence "get_state res sig = next_state t \<tau>' \<sigma> sig"
      by auto
    also have  "... =  (let m = \<tau>' maxtime in override_on \<sigma> (the \<circ> m) (dom m)) sig"
      unfolding next_state_def \<open>next_time t \<tau>' = maxtime\<close> by auto
    also have "... = signal_of (\<sigma> sig) \<tau>' sig maxtime"
      using \<open>next_time t \<tau>' = maxtime\<close> 
      by (smt "1.prems"(2) comp_apply domIff le_less next_time_at_least2 next_time_def option.exhaust_sel override_on_apply_in override_on_apply_notin signal_of_def trans_some_signal_of' zero_fun_def)
    also have "... = signal_of (\<sigma> sig) \<tau> sig maxtime"
      by (metis "1.hyps"(3) "1.prems"(1) b_conc_exec_modifies_local_strongest comp_def le_refl to_signal_equal_when_trans_equal_upto2)
    finally have ?case
      by auto }
  ultimately show ?case 
    by auto
next
  case (2 t maxtime \<tau> \<gamma> \<sigma> \<theta> def cs \<tau>')
  have "signal_of (\<sigma> sig) \<tau> sig maxtime = (\<sigma> sig)"
    apply (intro signal_of_def)
    using 2  by (metis b_conc_exec_modifies_local_strongest le_less_trans next_time_at_least2 zero_fun_def)
  thus ?case 
    by auto
next
  case (3 t maxtime \<tau> \<gamma> \<sigma> \<theta> def cs)
  then show ?case 
    by (metis comp_apply fst_conv quiet_def signal_of_empty snd_conv)
next
  case (4 t maxtime \<sigma> \<gamma> \<theta> def cs \<tau>)
  then show ?case by auto
qed

lemma get_event_never_empty:
  assumes "maxtime, t , \<sigma> , \<gamma> , \<theta>, def \<turnstile> <cs , \<tau>> \<leadsto> res"
  assumes "sig \<notin> set (signals_from cs)"
  assumes "\<tau> maxtime sig \<noteq> 0"
  assumes "non_stuttering (to_trans_raw_sig \<tau>) \<sigma> sig"
  assumes "t < maxtime"
  assumes "\<And>n. n < t \<Longrightarrow> \<tau> n = 0"
  assumes "conc_stmt_wf cs"
  shows   "sig \<in> get_event res"
  using assms
proof (induction)
  case (1 t maxtime \<tau> \<gamma> \<sigma> \<theta> def cs \<tau>' res)
  hence "next_time t \<tau>' < maxtime \<or> next_time t \<tau>' = maxtime"
    by auto
  moreover
  { assume "next_time t \<tau>' < maxtime"
    hence "(\<tau>'(next_time t \<tau>' := 0)) maxtime sig \<noteq> 0"
      using 1 b_conc_exec_modifies_local_strongest[OF 1(3) `sig \<notin> set (signals_from cs)`] 
      using calculation by auto
    have "non_stuttering (to_trans_raw_sig \<tau>') \<sigma> sig"
      using b_conc_exec_preserves_non_stuttering[OF 1(3) ] 1(9) 
      using "1.prems"(5) "1.prems"(6) by blast
    hence "non_stuttering (to_trans_raw_sig (\<tau>'(next_time t \<tau>' := 0))) (next_state t \<tau>' \<sigma>) sig"
      using non_stuttering_next  by (simp add: non_stuttering_next)
    have "\<And>n. n < next_time t \<tau>' \<Longrightarrow> (\<tau>'(next_time t \<tau>' := 0)) n = 0"
      using 1  by (simp add: next_time_at_least2)
    hence IH: "sig \<in> get_beh' res"
      using 1
      using \<open>(\<tau>'(next_time t \<tau>' := 0)) maxtime sig \<noteq> 0\<close> \<open>next_time t \<tau>' < maxtime\<close> \<open>non_stuttering (to_trans_raw_sig (\<tau>'(next_time t \<tau>' := 0))) (next_state t \<tau>' \<sigma>) sig\<close> by blast
    hence ?case
      by blast }
  moreover
  { assume "next_time t \<tau>' = maxtime"
    hence "res = (maxtime, next_state t \<tau>' \<sigma>, next_event t \<tau>' \<sigma>, Femto_VHDL_raw.add_to_beh2 \<sigma> \<theta> t def, \<tau>'(next_time t \<tau>' := 0))"
      using bau[OF 1(5)] by auto
    hence "get_event res = next_event t \<tau>' \<sigma>"
      by auto
    have "sig \<in> ... "
      unfolding next_event_alt_def
    proof -
      have "\<tau>' maxtime sig = \<tau> maxtime sig"
        using "1.hyps"(3) "1.prems"(1) b_conc_exec_modifies_local_strongest by fastforce
      hence "\<tau>' maxtime sig \<noteq> 0"
        using 1 by auto
      hence "next_state t \<tau>' \<sigma> sig = the (\<tau> maxtime sig)"
        by (metis \<open>\<tau>' maxtime sig = \<tau> maxtime sig\<close> \<open>next_time t \<tau>' = maxtime\<close> comp_apply domIff next_state_def override_on_apply_in zero_option_def)
      have "Femto_VHDL_raw.keys (to_trans_raw_sig \<tau> sig) \<noteq> {}"
        by (metis "1.prems"(2) Femto_VHDL_raw.keys_def dom_def dom_eq_empty_conv to_trans_raw_sig_def zero_option_def)
      have " maxtime \<in> Femto_VHDL_raw.keys (to_trans_raw_sig \<tau> sig)"
        by (simp add: "1.prems"(2) Femto_VHDL_raw.keys_def to_trans_raw_sig_def)
      have " t \<in> Femto_VHDL_raw.keys (to_trans_raw_sig \<tau> sig) \<or> t \<notin> Femto_VHDL_raw.keys (to_trans_raw_sig \<tau> sig)"
        by auto
      moreover
      { assume "t \<in> Femto_VHDL_raw.keys (to_trans_raw_sig \<tau> sig)"
        have "t < maxtime"
          using 1 by auto
        moreover have "(\<forall>k. t < k \<and> k < maxtime \<longrightarrow> k \<notin> Femto_VHDL_raw.keys (to_trans_raw_sig \<tau> sig))"
          using 1  by (metis Femto_VHDL_raw.keys_def \<open>next_time t \<tau>' = maxtime\<close>
          b_conc_exec_modifies_local_strongest domIff dom_def next_time_at_least2
          to_trans_raw_sig_def zero_fun_def zero_option_def)
        ultimately have " to_trans_raw_sig \<tau> sig t \<noteq> to_trans_raw_sig \<tau> sig maxtime"
          using \<open> non_stuttering (to_trans_raw_sig \<tau>) \<sigma> sig\<close>[unfolded non_stuttering_def]
          using \<open>maxtime \<in> Femto_VHDL_raw.keys (to_trans_raw_sig \<tau> sig)\<close> \<open>t \<in> Femto_VHDL_raw.keys
          (to_trans_raw_sig \<tau> sig)\<close> by blast
        moreover have "to_trans_raw_sig \<tau> sig t =  Some (\<sigma> sig)"
          by (metis (mono_tags) "1.hyps"(3) "1.prems"(1) "1.prems"(4) Femto_VHDL_raw.keys_def
          \<open>next_time t \<tau>' = maxtime\<close> \<open>t \<in> Femto_VHDL_raw.keys (to_trans_raw_sig \<tau> sig)\<close>
          b_conc_exec_modifies_local_strongest mem_Collect_eq next_time_at_least2
          to_trans_raw_sig_def zero_fun_def)
        moreover have "to_trans_raw_sig \<tau> sig maxtime = Some (next_state t \<tau>' \<sigma> sig)"
          by (metis \<open>\<tau>' maxtime sig = \<tau> maxtime sig\<close> \<open>\<tau>' maxtime sig \<noteq> 0\<close> \<open>next_state t \<tau>' \<sigma> sig =
          the (\<tau> maxtime sig)\<close> option.exhaust_sel to_trans_raw_sig_def zero_option_def) 
        ultimately have " sig \<in> {sig. \<sigma> sig \<noteq> next_state t \<tau>' \<sigma> sig}"
          by auto }
      moreover
      { assume "t \<notin> Femto_VHDL_raw.keys (to_trans_raw_sig \<tau> sig)"
        have "(LEAST k. k \<in> Femto_VHDL_raw.keys (to_trans_raw_sig \<tau> sig)) = maxtime"
        proof (rule Least_equality)
          show "maxtime \<in> Femto_VHDL_raw.keys (to_trans_raw_sig \<tau> sig)"
            using \<open>maxtime \<in> Femto_VHDL_raw.keys (to_trans_raw_sig \<tau> sig)\<close> by blast
        next
          { fix y 
            assume "y < maxtime"
            hence " y \<notin> Femto_VHDL_raw.keys (to_trans_raw_sig \<tau> sig)"
              unfolding Femto_VHDL_raw.keys_def to_trans_raw_sig_def zero_option_def
              by (metis (mono_tags, lifting) "1.hyps"(3) "1.prems"(1) \<open>next_time t \<tau>' = maxtime\<close>
              b_conc_exec_modifies_local_strongest mem_Collect_eq next_time_at_least2 zero_fun_def
              zero_option_def) }
          thus "\<And>y. y \<in> Femto_VHDL_raw.keys (to_trans_raw_sig \<tau> sig) \<Longrightarrow> maxtime \<le> y"
            using le_less_linear by blast          
        qed 
        hence " sig \<in> {sig. \<sigma> sig \<noteq> next_state t \<tau>' \<sigma> sig}"
          using \<open> non_stuttering (to_trans_raw_sig \<tau>) \<sigma> sig\<close>[unfolded non_stuttering_def]
          by (metis (mono_tags) \<open>Femto_VHDL_raw.keys (to_trans_raw_sig \<tau> sig) \<noteq> {}\<close> \<open>next_state t \<tau>' \<sigma> sig = the (\<tau> maxtime sig)\<close> mem_Collect_eq to_trans_raw_sig_def) }
      ultimately show " sig \<in> {sig. \<sigma> sig \<noteq> next_state t \<tau>' \<sigma> sig}"
        by auto
    qed
    hence ?case
      using \<open>get_beh' res = next_event t \<tau>' \<sigma>\<close> by blast }
  ultimately show ?case 
    by auto
next
  case (2 t maxtime \<tau> \<gamma> \<sigma> \<theta> def cs \<tau>')
  then show ?case 
    by (metis b_conc_exec_modifies_local_strongest until_next_time_zero zero_fun_def)
next
  case (3 t maxtime \<tau> \<gamma> \<sigma> \<theta> def cs)
  then show ?case 
    unfolding quiet_def zero_option_def zero_fun_def by presburger
next
  case (4 t maxtime \<sigma> \<gamma> \<theta> def cs \<tau>)
  then show ?case by auto
qed

lemma get_event_never_empty':
  assumes "maxtime, t , \<sigma> , \<gamma> , \<theta>, def \<turnstile> <cs , \<tau>> \<leadsto> res"
  assumes "sig \<notin> set (signals_from cs)"
  assumes "\<tau> maxtime sig \<noteq> 0"
  assumes "non_stuttering (to_trans_raw_sig \<tau>) \<sigma> sig"
  assumes "t < maxtime"
  assumes "\<And>n. n < t \<Longrightarrow> \<tau> n = 0"
  assumes "conc_stmt_wf cs"
  shows   "get_event res \<noteq> {}"
  using get_event_never_empty assms 
  by (metis empty_iff)

lemma bau_signal_of:
  assumes "maxtime, t , \<sigma> , \<gamma> , \<theta>, def \<turnstile> <cs , \<tau>> \<leadsto> res"
  assumes "sig \<notin> set (signals_from cs)"
  assumes "maxtime \<le> i"
  assumes "\<And>n. n < t \<Longrightarrow> \<tau> n = 0"
  shows   "signal_of (\<sigma> sig) \<tau>  sig i = signal_of (get_state res sig) (get_trans res) sig i"
  using assms
proof (induction)
  case (1 t maxtime \<tau> \<gamma> \<sigma> \<theta> def cs \<tau>' res)
  hence "next_time t \<tau>' \<le> i "
    by linarith
  hence IH: "signal_of (next_state t \<tau>' \<sigma> sig) (\<tau>'(next_time t \<tau>' := 0)) sig i = signal_of (get_state res sig) (get_trans res) sig i"
    using 1 next_time_at_least2 by fastforce
  have "\<And>i. \<tau> i sig = \<tau>' i sig"
    using b_conc_exec_modifies_local_strongest[OF 1(3) 1(7)] by auto
  have "signal_of (\<sigma> sig) \<tau> sig i = signal_of (next_state t \<tau>' \<sigma> sig) \<tau>' sig i"
  proof (rule b_conc_exec_does_not_modify_signals2)
    show "\<And>n. n < t \<Longrightarrow> \<tau> n = 0"
      by (simp add: "1.prems"(3))
  next
    show "t , \<sigma> , \<gamma> , \<theta>, def  \<turnstile> <cs , \<tau>> \<longrightarrow>\<^sub>c \<tau>'"
      using 1 by auto
  next
    show "sig \<notin> set (signals_from cs)"
      using 1 by auto
  next
    show " next_time t \<tau>' \<le> i"
      using ` next_time t \<tau>' \<le> i` by auto
  qed
  also have "... = signal_of (next_state t \<tau>' \<sigma> sig) (\<tau>'(next_time t \<tau>' := 0)) sig i"
    by (smt comp_def next_state_def next_time_at_least2 override_on_apply_in signal_of_rem_curr_trans_at_t)
  finally show ?case
    unfolding IH by auto   
next
  case (2 t maxtime \<tau> \<gamma> \<sigma> \<theta> def cs \<tau>')
  then show ?case 
    by (metis b_conc_exec_modifies_local_strongest comp_apply fst_conv less_or_eq_imp_le snd_conv
        to_signal_equal_when_trans_equal_upto2)
next
  case (3 t maxtime \<tau> \<gamma> \<sigma> \<theta> def cs)
  then show ?case  
    by (metis comp_apply fst_conv quiet_def snd_conv)
next
  case (4 t maxtime \<sigma> \<gamma> \<theta> def cs \<tau>)
  then show ?case by auto
qed

lemma b_simulate_fin_get_trans_gt_maxtime:
  assumes "maxtime, t , \<sigma> , \<gamma> , \<theta>, def \<turnstile> <cs , \<tau>> \<leadsto> res"
  assumes "sig \<notin> set (signals_from cs)"
  shows   "\<forall>n > maxtime. get_trans res n sig = \<tau> n sig"
  using assms
proof (induction)
  case (1 t maxtime \<tau> \<gamma> \<sigma> \<theta> def cs \<tau>' res)
  hence " \<forall>n>maxtime. get_trans res n sig = (\<tau>'(next_time t \<tau>' := 0)) n sig"
    by auto
  moreover have "\<And>n. \<tau> n sig = \<tau>' n sig"
    using b_conc_exec_modifies_local_strongest[OF 1(3) 1(7)] by auto
  ultimately show ?case
    using 1 by auto
next
  case (2 t maxtime \<tau> \<gamma> \<sigma> \<theta> def cs \<tau>')
  then show ?case 
    using b_conc_exec_modifies_local_strongest by fastforce
next
  case (3 t maxtime \<tau> \<gamma> \<sigma> \<theta> def cs)
  then show ?case 
    by (metis comp_apply quiet_def snd_conv)
next
  case (4 t maxtime \<sigma> \<gamma> \<theta> def cs \<tau>)
  then show ?case by auto
qed


theorem nand4_correctness:
  assumes "b_simulate (Suc i) def nand4 \<tau> res"
  assumes "to_trans_raw_sig \<tau> C = 0"
  assumes "conc_wt \<Gamma> nand4" and "styping \<Gamma> def" and "\<Gamma> C = Bty" and "ttyping \<Gamma> \<tau>"
  assumes "\<forall>s. non_stuttering (to_trans_raw_sig \<tau>) def s"
  shows "bval_of (signal_of (def C) (get_beh res) C i) \<longleftrightarrow>
          \<not> (bval_of (signal_of (def A) \<tau> A i) \<and> bval_of (signal_of (def B) \<tau> B i))"
proof (cases "inf_time (to_trans_raw_sig \<tau>) A i = None \<and> inf_time (to_trans_raw_sig \<tau>) B i = None")
  case True
  hence "signal_of (def A) \<tau> A i = def A" and "signal_of (def B) \<tau> B i = def B"
    unfolding to_signal_def comp_def by auto
  have "\<forall>n \<le> i. \<tau> n A = 0"
    using True  by (metis (full_types) inf_time_noneE2 leI less_irrefl_nat to_trans_raw_sig_def)
  have "\<forall>n \<le> i. \<tau> n B = 0"
    using True by (metis (full_types) inf_time_noneE2 leI less_irrefl_nat to_trans_raw_sig_def)
  obtain \<tau>' t' \<sigma>' \<gamma>' where "init' 0 def {} 0 def nand4 \<tau> \<tau>'" and "next_time  0 \<tau>' = t'" and "next_state 0 \<tau>' def = \<sigma>'" and "next_event 0 \<tau>' def = \<gamma>'"
    using bsim[OF assms(1)] by meson
  have  bigstep: "Suc i, t', \<sigma>', \<gamma>', 0, def \<turnstile> <nand4, \<tau>'(t' := 0)> \<leadsto> res"
    using bsim[OF assms(1)] 
    by (metis \<open>init' 0 def {} 0 def nand4 \<tau> \<tau>'\<close> \<open>next_event 0 \<tau>' def = \<gamma>'\<close> \<open>next_state 0 \<tau>' def = \<sigma>'\<close> \<open>next_time 0 \<tau>' = t'\<close> assms(1) bsimulate_obt_big_step)
  have trans_removal: "\<And>n. n < t' \<Longrightarrow> (\<tau>'(t' := 0)) n = 0"
    using \<open>next_time 0 \<tau>' = t'\<close> next_time_at_least2 by auto
  have "\<Gamma> A = Bty" and "\<Gamma> B = Bty"
    using assms  by (metis bexp_wt_cases(4) bexp_wt_cases_slice(2) conc_wt_cases(1) nand4_def seq_wt_cases(4))+
  consider (good_default) "bval_of (def C) \<longleftrightarrow> \<not> (bval_of (def A) \<and> bval_of (def B))" | (bad_default) "bval_of (def C) \<noteq> (\<not> (bval_of (def A) \<and> bval_of (def B)))"
    by auto
  then show ?thesis 
  proof (cases)
    case good_default
    have " \<tau>' = preempt_raw C \<tau> 0"
    proof (rule init'_cases(1)[OF  \<open>init' 0 def {} 0 def nand4 \<tau> \<tau>'\<close>[unfolded nand4_def]])
      assume asm: "0 , def , {} , 0, def  \<turnstile> <Bassign_trans C (Bnand (Bsig A) (Bsig B)) 0 , \<tau>> \<longrightarrow>\<^sub>s \<tau>' "
      show "\<tau>' = preempt_raw C \<tau> 0"
      proof (rule seq_cases_trans[OF asm])
        fix x
        assume "0 , def , {} , 0, def  \<turnstile> Bnand (Bsig A) (Bsig B) \<longrightarrow>\<^sub>b x"
        have "0 , def , {} , 0, def  \<turnstile> Bsig A \<longrightarrow>\<^sub>b def A"
          by (simp add: beval_raw.intros(1))
        have "0 , def , {} , 0, def  \<turnstile> Bsig B \<longrightarrow>\<^sub>b def B"
          by (simp add: beval_raw.intros(1))
        have "def A = Bv (bval_of (def A))"
          using \<open>\<Gamma> A = Bty\<close> \<open>styping \<Gamma> def\<close> 
          by (metis \<open>signal_of (def A) \<tau> A i = def A\<close> assms(6) signal_of_preserve_well_typedness ty.distinct(1) type_of.simps(2) val.exhaust_sel)
        moreover have "def B = Bv (bval_of (def B))"
          using \<open>\<Gamma> B = Bty\<close> \<open>styping \<Gamma> def\<close> 
          by (metis \<open>signal_of (def B) \<tau> B i = def B\<close> assms(6) signal_of_preserve_well_typedness ty.distinct(1) type_of.simps(2) val.exhaust_sel)
        ultimately have "x = Bv (\<not> (bval_of (def A) \<and> bval_of (def B)))"
          using \<open>0 , def , {} , 0, def  \<turnstile> Bnand (Bsig A) (Bsig B) \<longrightarrow>\<^sub>b x\<close> 
          by (metis (no_types, hide_lams) beval_raw.intros(1) beval_raw.intros(12) beval_raw_deterministic)
        moreover have "def C = Bv (bval_of (def C))"
          using \<open>\<Gamma> C = Bty\<close>  by (metis assms(4) styping_def ty.simps(3) type_of.simps(2) val.exhaust_sel)
        ultimately have "x = def C"
          using good_default by auto
        assume " trans_post_raw C x (def C) \<tau> 0 0 = \<tau>'"
        moreover have "\<not> post_necessary_raw (0 - 1) \<tau> 0 C x (def C)"
          unfolding post_necessary_raw_correctness using \<open>x = def C\<close> assms(2) unfolding to_trans_raw_sig_def
          by (metis zero_fun_def zero_option_def)
        ultimately show ?thesis
          unfolding trans_post_raw_def  by auto
      qed
    qed
    hence "to_trans_raw_sig \<tau>' C = 0"
      using assms(2) unfolding preempt_raw_def to_trans_raw_sig_def zero_fun_def zero_option_def
      fun_upd_def by auto
    have "\<tau> \<noteq> 0 \<or> \<tau> = 0"
      by auto
    moreover
    { assume "\<tau> \<noteq> 0"
      hence "\<tau>' \<noteq> 0"
        using \<open>to_trans_raw_sig \<tau> C = 0\<close>
        unfolding \<open>\<tau>' = preempt_raw C \<tau> 0\<close> preempt_raw_def to_trans_raw_sig_def 
        by (smt fun_upd_triv less_Suc_eq_le less_irrefl_nat next_time_at_least next_time_def zero_fun_def zero_option_def)
      have "i < next_time 0 \<tau>'"
      proof (rule ccontr)
        assume "\<not> i < next_time 0 \<tau>'" hence "next_time 0 \<tau>' \<le> i" by auto
        hence "(LEAST n. dom (\<tau>' n) \<noteq> {}) \<le> i"
          unfolding next_time_def using \<open>\<tau>' \<noteq> 0\<close> by auto
        have "\<exists>n. dom (\<tau>' n) \<noteq> {}"
          using \<open>\<tau>' \<noteq> 0\<close> unfolding dom_def zero_fun_def zero_option_def  by fastforce
        hence "dom (\<tau>' (LEAST n. dom (\<tau>' n) \<noteq> {})) \<noteq> {}"
          by (metis (mono_tags) LeastI)
        have "\<tau>' (LEAST n. dom (\<tau>' n) \<noteq> {}) A = None"
          using \<open>\<forall>n \<le> i. \<tau> n A = 0\<close> \<open>(LEAST n. dom (\<tau>' n) \<noteq> {}) \<le> i\<close> unfolding \<open>\<tau>' = preempt_raw C \<tau> 0\<close>
          preempt_raw_def  by (simp add: zero_option_def)
        moreover have "\<tau>' (LEAST n. dom (\<tau>' n) \<noteq> {}) B = None"
          using \<open>\<forall>n \<le> i. \<tau> n B = 0\<close> \<open>(LEAST n. dom (\<tau>' n) \<noteq> {}) \<le> i\<close> unfolding \<open>\<tau>' = preempt_raw C \<tau> 0\<close>
          preempt_raw_def  by (simp add: zero_option_def)
        moreover have "\<tau>' (LEAST n. dom (\<tau>' n) \<noteq> {}) C = None"
          unfolding \<open>\<tau>' = preempt_raw C \<tau> 0\<close> preempt_raw_def  by (simp add: zero_option_def)
        ultimately have "dom (\<tau>' (LEAST n. dom (\<tau>' n) \<noteq> {})) = {}"
          unfolding dom_def  by (metis (mono_tags, lifting) empty_Collect_eq sig.exhaust)
        thus False
          using \<open>dom (\<tau>' (LEAST n. dom (\<tau>' n) \<noteq> {})) \<noteq> {}\<close> by blast
      qed
      have "t' \<le> Suc i"
        using bigstep by (induction) auto
      hence "t' = Suc i"
        using Suc_leI \<open>i < next_time 0 \<tau>'\<close> \<open>next_time 0 \<tau>' = t'\<close> le_antisym by blast
      hence "res = (Suc i, \<sigma>', \<gamma>', 0, \<tau>'(t' := 0))"
        using bau[OF bigstep] by auto
      hence "get_beh res = 0"
        by auto
      hence "signal_of (def C) (get_beh res) C i = def C"
        using signal_of_empty by force
      hence ?thesis
        using \<open>signal_of (def A) \<tau> A i = def A\<close> \<open>signal_of (def B) \<tau> B i = def B\<close> good_default by auto }
    moreover
    { assume "\<tau> = 0"
      hence "\<tau>' = 0"
        using \<open>to_trans_raw_sig \<tau> C = 0\<close>
        unfolding \<open>\<tau>' = preempt_raw C \<tau> 0\<close> preempt_raw_def  by (simp add: zero_fun_def zero_option_def)
      moreover hence "\<gamma>' = {}"
        by (smt Collect_empty_eq \<open>next_event 0 \<tau>' def = \<gamma>'\<close> domIff next_event_def zero_fun_def zero_option_def)
      ultimately have "quiet (\<tau>'(t':=0)) \<gamma>'"
        unfolding quiet_def fun_upd_def zero_fun_def zero_option_def by auto
      hence "res = (Suc i, \<sigma>', \<gamma>', 0, 0)"
        using bau[OF bigstep]  by (smt quiet_def)
      hence ?thesis
        using \<open>signal_of (def A) \<tau> A i = def A\<close> \<open>signal_of (def B) \<tau> B i = def B\<close> good_default 
        by (metis comp_def fst_conv signal_of_empty snd_conv) }
    ultimately show ?thesis
      by blast
  next
    case bad_default
    have "\<tau>' = post_raw C (Bv (\<not> (bval_of (def A) \<and> bval_of (def B)))) \<tau> 0 \<and> post_necessary_raw (0 - 1) \<tau> 0 C (Bv (\<not> (bval_of (def A) \<and> bval_of (def B)))) (def C)"
    proof (rule init'_cases(1)[OF  \<open>init' 0 def {} 0 def nand4 \<tau> \<tau>'\<close>[unfolded nand4_def]])
      assume asm: "0 , def , {} , 0, def  \<turnstile> <Bassign_trans C (Bnand (Bsig A) (Bsig B)) 0 , \<tau>> \<longrightarrow>\<^sub>s \<tau>' "
      show "\<tau>' = post_raw C (Bv (\<not> (bval_of (def A) \<and> bval_of (def B)))) \<tau> 0 \<and> post_necessary_raw (0 - 1) \<tau> 0 C (Bv (\<not> (bval_of (def A) \<and> bval_of (def B)))) (def C)"
      proof (rule seq_cases_trans[OF asm])
        fix x
        assume "0 , def , {} , 0, def  \<turnstile> Bnand (Bsig A) (Bsig B) \<longrightarrow>\<^sub>b x"
        have "0 , def , {} , 0, def  \<turnstile> Bsig A \<longrightarrow>\<^sub>b def A"
          by (simp add: beval_raw.intros(1))
        have "0 , def , {} , 0, def  \<turnstile> Bsig B \<longrightarrow>\<^sub>b def B"
          by (simp add: beval_raw.intros(1))
        have "def A = Bv (bval_of (def A))"
          using \<open>\<Gamma> A = Bty\<close> \<open>styping \<Gamma> def\<close> 
          by (metis \<open>signal_of (def A) \<tau> A i = def A\<close> assms(6) signal_of_preserve_well_typedness ty.distinct(1) type_of.simps(2) val.exhaust_sel)
        moreover have "def B = Bv (bval_of (def B))"
          using \<open>\<Gamma> B = Bty\<close> \<open>styping \<Gamma> def\<close> 
          by (metis \<open>signal_of (def B) \<tau> B i = def B\<close> assms(6) signal_of_preserve_well_typedness ty.distinct(1) type_of.simps(2) val.exhaust_sel)
        ultimately have x_def: "x = Bv (\<not> (bval_of (def A) \<and> bval_of (def B)))"
          using \<open>0 , def , {} , 0, def  \<turnstile> Bnand (Bsig A) (Bsig B) \<longrightarrow>\<^sub>b x\<close> 
          by (metis (no_types, hide_lams) beval_raw.intros(1) beval_raw.intros(12) beval_raw_deterministic)
        moreover have "def C = Bv (bval_of (def C))"
          using \<open>\<Gamma> C = Bty\<close>  by (metis assms(4) styping_def ty.simps(3) type_of.simps(2) val.exhaust_sel)
        ultimately have "x \<noteq> def C"
          using bad_default by auto
        assume " trans_post_raw C x (def C) \<tau> 0 0 = \<tau>'"
        moreover have "post_necessary_raw (0) \<tau> 0 C x (def C)"
          unfolding post_necessary_raw_correctness2 using \<open>x \<noteq> def C\<close> assms(2) unfolding to_trans_raw_sig_def
          by (metis zero_fun_def zero_option_def)
        ultimately show ?thesis
          unfolding trans_post_raw_def x_def  by auto
      qed
    qed
    hence \<tau>'_def: "\<tau>' = post_raw C (Bv (\<not> (bval_of (def A) \<and> bval_of (def B)))) \<tau> 0" and "post_necessary_raw 0 \<tau> 0 C (Bv (\<not> (bval_of (def A) \<and> bval_of (def B)))) (def C)"
      by auto
    hence "next_time  0 \<tau>' = 0"
      by (metis (full_types) fun_upd_eqD fun_upd_triv le0 nat_less_le next_time_at_least2 option.distinct(1) post_raw_def zero_fun_def zero_option_def)
    have "A \<notin> next_event 0 \<tau>' def"
    proof (rule ccontr)
      assume "\<not> A \<notin> next_event 0 \<tau>' def"
      hence "def A \<noteq> next_state 0 \<tau>' def A"
        unfolding next_event_alt_def by auto
      moreover have "next_state 0 \<tau>' def A = def A"
        unfolding next_state_def Let_def \<open>next_time 0 \<tau>' = 0\<close> comp_def dom_def \<tau>'_def 
        using \<open>\<forall>n \<le> i. \<tau> n A = 0\<close> 
        by (metis (mono_tags) \<open>next_time 0 \<tau>' = 0\<close> \<tau>'_def fun_upd_other le0 mem_Collect_eq override_on_apply_notin post_raw_def sig.distinct(3) zero_option_def)
      ultimately show False
        by auto
    qed
    have "B \<notin> next_event 0 \<tau>' def"
    proof (rule ccontr)
      assume "\<not> B \<notin> next_event 0 \<tau>' def"
      hence "def B \<noteq> next_state 0 \<tau>' def B"
        unfolding next_event_alt_def by auto
      moreover have "next_state 0 \<tau>' def B = def B"
        unfolding next_state_def Let_def \<open>next_time 0 \<tau>' = 0\<close> comp_def dom_def \<tau>'_def 
        using \<open>\<forall>n \<le> i. \<tau> n B = 0\<close> 
        by (metis (mono_tags, hide_lams) \<open>next_time 0 \<tau>' = 0\<close> \<tau>'_def calculation domIff
        fun_upd_other le0 next_state_def override_on_apply_notin post_raw_def sig.distinct(5)
        zero_option_def)
      ultimately show False
        by auto
    qed
    show ?thesis 
    proof -
      note True = \<open>A \<notin> next_event 0 \<tau>' def\<close> \<open>B \<notin> next_event 0 \<tau>' def\<close>
      hence "next_event 0 \<tau>' def = {C}"
      proof - 
        have "\<And>sig. def sig \<noteq> next_state 0 \<tau>' def sig \<Longrightarrow> sig = C"
        proof (rule ccontr)
          fix sig
          assume "sig \<noteq> C"
          hence "sig = A \<or> sig = B"
            using sig.exhaust by blast
          hence "next_state 0 \<tau>' def sig = def sig"
            unfolding next_state_def \<open>next_time 0 \<tau>' = 0\<close> \<tau>'_def Let_def comp_def 
            by (metis \<open>\<forall>n\<le>i. \<tau> n A = 0\<close> \<open>\<forall>n\<le>i. \<tau> n B = 0\<close> \<open>next_time 0 \<tau>' = 0\<close> \<open>sig \<noteq> C\<close> \<tau>'_def domIff fun_upd_other leD not_less_eq_eq override_on_apply_notin post_raw_def zero_less_Suc zero_option_def)
          moreover assume "def sig \<noteq> next_state 0 \<tau>' def sig"
          ultimately show False
            by auto
        qed
        moreover have "def C \<noteq> next_state 0 \<tau>' def C"
          using bad_default \<open>post_necessary_raw 0 \<tau> 0 C (Bv (\<not> (bval_of (def A) \<and> bval_of (def B)))) (def C)\<close> unfolding post_necessary_raw_correctness2
          by (smt \<open>next_time 0 \<tau>' = 0\<close> \<tau>'_def domIff fun_upd_same next_state_def o_def option.distinct(1) option.sel override_on_def post_raw_def val.sel(1))
        ultimately show ?thesis
          unfolding next_event_alt_def  by (intro equalityI)auto
      qed
      have "t' < Suc i"
        using \<open>next_time 0 \<tau>' = 0\<close> \<open>next_time 0 \<tau>' = t'\<close> less_Suc_eq_0_disj by blast
      have "\<not> quiet (\<tau>'(t':=0)) \<gamma>'"
        using \<open>next_event 0 \<tau>' def = \<gamma>'\<close> \<open>next_event 0 \<tau>' def = {C}\<close> quiet_def by force
      have "t', \<sigma>', \<gamma>', 0, def \<turnstile> <nand4, \<tau>'(t':=0)> \<longrightarrow>\<^sub>c \<tau>'(t':=0)"
        unfolding nand4_def
        apply (intro b_conc_exec.intros(1))
        using \<open>next_event 0 \<tau>' def = {C}\<close> by (simp add: \<open>next_event 0 \<tau>' def = \<gamma>'\<close>)
      have "next_time t' (\<tau>'(t':=0)) \<le> Suc i \<or> Suc i < next_time t' (\<tau>'(t':=0))"
        by auto
      moreover
      { assume "Suc i < next_time t' (\<tau>'(t':=0))"
        hence "res = (Suc i, \<sigma>', {}, Femto_VHDL_raw.add_to_beh2 \<sigma>' 0 t' def, \<tau>'(t':=0))"
          using bau[OF bigstep]
          by (smt \<open>\<not> quiet (\<tau>'(t' := 0)) \<gamma>'\<close> \<open>next_time 0 \<tau>' = 0\<close> \<open>next_time 0 \<tau>' = t'\<close> \<open>t' , \<sigma>' ,
          \<gamma>' , 0, def \<turnstile> <nand4 , \<tau>' (t' := 0)> \<longrightarrow>\<^sub>c \<tau>'(t' := 0)\<close> \<open>t' < Suc i\<close>
          b_conc_exec_deterministic leD le_numeral_extra(3))
        hence "get_beh res = Femto_VHDL_raw.add_to_beh2 \<sigma>' 0 0 def"
          using \<open>next_time 0 \<tau>' = 0\<close> \<open>next_time 0 \<tau>' = t'\<close> by auto
        hence "signal_of (def C) (get_beh res) C i = \<sigma>' C"
          using signal_of_add_to_beh2'  by (metis (full_types) zero_fun_def zero_le)
        also have "... = the (\<tau>' 0 C)"
          by (smt \<open>next_state 0 \<tau>' def = \<sigma>'\<close> \<open>next_time 0 \<tau>' = 0\<close> \<tau>'_def comp_def domIff fun_upd_eqD fun_upd_triv next_state_def option.distinct(1) override_on_def post_raw_def)
        also have "... = (Bv (\<not> (bval_of (def A) \<and> bval_of (def B)))) "
          unfolding \<tau>'_def post_raw_def by auto
        finally have "bval_of (signal_of (def C) (get_beh res) C i) \<longleftrightarrow> \<not> (bval_of (def A) \<and> bval_of (def B))"
          by auto
        hence ?thesis
          using \<open>signal_of (def A) \<tau> A i = def A\<close> \<open>signal_of (def B) \<tau> B i = def B\<close> by auto }
      moreover
      { assume "next_time t' (\<tau>'(t':=0)) \<le> Suc i"
        hence bigstep2: "Suc i, next_time t' (\<tau>'(t':=0)) , next_state t' (\<tau>'(t':=0)) \<sigma>' , next_event t' (\<tau>'(t':=0)) \<sigma>' , Femto_VHDL_raw.add_to_beh2 \<sigma>' 0 t' def, def \<turnstile> <nand4 , (\<tau>'(t':=0))(next_time t' (\<tau>'(t':=0)) := 0)> \<leadsto> res"
          using bau[OF bigstep] 
          by (smt \<open>\<not> quiet (\<tau>'(t' := 0)) \<gamma>'\<close> \<open>t' , \<sigma>' , \<gamma>' , 0, def \<turnstile> <nand4 , \<tau>' (t' := 0)> \<longrightarrow>\<^sub>c \<tau>'(t' := 0)\<close> \<open>t' < Suc i\<close> bigstep case_bau)
        have "(\<tau>'(0:=0)) = 0 \<or> (\<tau>'(0:=0) \<noteq> 0)"
          by auto
        moreover
        { assume "\<tau>'(0:=0) = 0"
          hence " (\<tau>'(t':=0))(next_time t' (\<tau>'(t':=0)) := 0) = 0"
            by (metis \<open>next_time 0 \<tau>' = 0\<close> \<open>next_time 0 \<tau>' = t'\<close> fun_upd_triv zero_fun_def)
          moreover hence "next_event t' (\<tau>'(t':=0)) \<sigma>' = {}"
            by (metis (mono_tags) Collect_empty_eq \<open>\<tau>'(0 := 0) = 0\<close> \<open>next_time 0 \<tau>' = 0\<close> \<open>next_time
            0 \<tau>' = t'\<close> dom_eq_empty_conv next_event_alt_def next_state_def override_on_emptyset
            zero_fun_def zero_option_def)
          ultimately have "quiet ((\<tau>'(t':=0))(next_time t' (\<tau>'(t':=0)) := 0)) (next_event t' (\<tau>'(t':=0)) \<sigma>') "
            unfolding quiet_def  by auto
          hence "res = (Suc i, next_state t' (\<tau>'(t':=0)) \<sigma>', next_event t' (\<tau>'(t':=0)) \<sigma>', Femto_VHDL_raw.add_to_beh2 \<sigma>' 0 t' def, 0)"
            using bau[OF bigstep2]  using \<open>\<tau>'(t' := 0, next_time t' (\<tau>'(t' := 0)) := 0) = 0\<close> by blast
          hence "get_beh res = Femto_VHDL_raw.add_to_beh2 \<sigma>' 0 0 def"
            using \<open>next_time 0 \<tau>' = 0\<close> \<open>next_time 0 \<tau>' = t'\<close> by auto
          hence "signal_of (def C) (get_beh res) C i = \<sigma>' C"
            using signal_of_add_to_beh2'  by (metis (full_types) zero_fun_def zero_le)
          also have "... = the (\<tau>' 0 C)"
            by (smt \<open>next_state 0 \<tau>' def = \<sigma>'\<close> \<open>next_time 0 \<tau>' = 0\<close> \<tau>'_def comp_apply domIff fun_upd_same next_state_def option.distinct(1) override_on_def post_raw_def)
          also have "... = (Bv (\<not> (bval_of (def A) \<and> bval_of (def B))))"
            unfolding \<tau>'_def  by (simp add: post_raw_def)
          finally have ?thesis
            using \<open>signal_of (def A) \<tau> A i = def A\<close> \<open>signal_of (def B) \<tau> B i = def B\<close> by auto }
        moreover
        { assume "\<tau>'(0:=0) \<noteq> 0"
          have "i < next_time 0 (\<tau>'(0 := 0))"
          proof (rule ccontr)
            assume "\<not> i < next_time 0 (\<tau>'(0:=0))" hence "next_time 0 (\<tau>'(0:=0)) \<le> i"
              by auto
            hence "(LEAST n. dom ((\<tau>'(0 := 0)) n) \<noteq> {}) \<le> i"
              using \<open>\<tau>'(0:=0) \<noteq> 0\<close> unfolding next_time_def by auto
            have "\<exists>n. dom ((\<tau>'(0 := 0)) n) \<noteq> {}"
              using \<open>\<tau>'(0:=0) \<noteq> 0\<close> unfolding dom_def zero_fun_def zero_option_def  by (metis dom_def dom_eq_empty_conv)
            hence "dom ((\<tau>'(0 := 0)) (LEAST n. dom ((\<tau>'(0 := 0)) n) \<noteq> {})) \<noteq> {}"
              by (metis (mono_tags, lifting) LeastI_ex)
            moreover have "C \<notin> dom ((\<tau>'(0 := 0)) (LEAST n. dom ((\<tau>'(0 := 0)) n) \<noteq> {}))"
              using \<tau>'_def unfolding post_raw_def  by (simp add: zero_fun_def zero_option_def)
            moreover have "A \<notin> dom ((\<tau>'(0 := 0)) (LEAST n. dom ((\<tau>'(0 := 0)) n) \<noteq> {}))"
              using \<open>(LEAST n. dom ((\<tau>'(0 := 0)) n) \<noteq> {}) \<le> i\<close> \<tau>'_def \<open>\<forall>n \<le> i. \<tau> n A = 0\<close>
              by (simp add: domIff post_raw_def zero_fun_def zero_option_def)
            moreover have "B \<notin> dom ((\<tau>'(0 := 0)) (LEAST n. dom ((\<tau>'(0 := 0)) n) \<noteq> {}))"
              using \<open>(LEAST n. dom ((\<tau>'(0 := 0)) n) \<noteq> {}) \<le> i\<close> \<tau>'_def \<open>\<forall>n \<le> i. \<tau> n B = 0\<close>
              by (simp add: domIff post_raw_def zero_fun_def zero_option_def)
            ultimately show False
              using sig.exhaust 
            proof -
              obtain ss :: "(sig \<Rightarrow> val option) \<Rightarrow> sig" where
                f1: "\<And>f. f (ss f) \<noteq> None \<or> dom f = {}"
                by (meson dom_eq_empty_conv)
              then have "\<And>f. f C \<noteq> None \<or> ss f = B \<or> ss f = A \<or> dom f = {}"
                by (metis (full_types) sig.exhaust)
              then show ?thesis
                using f1 by (metis (lifting) \<open>A \<notin> dom ((\<tau>'(0 := 0)) (LEAST n. dom ((\<tau>'(0 := 0)) n) \<noteq> {}))\<close> \<open>B \<notin> dom ((\<tau>'(0 := 0)) (LEAST n. dom ((\<tau>'(0 := 0)) n) \<noteq> {}))\<close> \<open>C \<notin> dom ((\<tau>'(0 := 0)) (LEAST n. dom ((\<tau>'(0 := 0)) n) \<noteq> {}))\<close> \<open>dom ((\<tau>'(0 := 0)) (LEAST n. dom ((\<tau>'(0 := 0)) n) \<noteq> {})) \<noteq> {}\<close> domIff)
            qed
          qed
          hence "i < next_time t' (\<tau>'(t' := 0))"
            using \<open>next_time 0 \<tau>' = 0\<close> \<open>next_time 0 \<tau>' = t'\<close> by auto
          have "\<And>n. n < next_time t' (\<tau>'(t' := 0)) \<Longrightarrow> (\<tau>'(t' := 0, next_time t' (\<tau>'(t' := 0)) := 0)) n = 0"
            using next_time_at_least2 by fastforce
          hence " \<And>n. n < next_time t' (\<tau>'(t' := 0)) \<Longrightarrow> Femto_VHDL_raw.add_to_beh2 \<sigma>' 0 t' def n = get_beh res n"
            using beh_res[OF bigstep2 _ `next_time t' (\<tau>'(t' := 0)) \<le> Suc i` ] by auto
          hence "\<And>n. n \<le> i \<Longrightarrow> Femto_VHDL_raw.add_to_beh2 \<sigma>' 0 t' def n = get_beh res n"
            by (simp add: \<open>i < next_time t' (\<tau>'(t' := 0))\<close> le_less_trans)
          hence "signal_of (def C) (get_beh res) C i = \<sigma>' C"
            by (smt \<open>i < next_time t' (\<tau>'(t' := 0))\<close> \<open>t' < Suc i\<close> b_simulate_fin.simps bigstep2
            comp_def fst_conv leD le_Suc_eq nat_less_le signal_of_add_to_beh2' snd_conv
            zero_fun_def)
          also have "... = the (\<tau>' 0 C)"
            by (smt \<open>next_state 0 \<tau>' def = \<sigma>'\<close> \<open>next_time 0 \<tau>' = 0\<close> \<tau>'_def comp_apply domIff fun_upd_same next_state_def option.distinct(1) override_on_def post_raw_def)
          also have "... = (Bv (\<not> (bval_of (def A) \<and> bval_of (def B))))"
            unfolding \<tau>'_def  by (simp add: post_raw_def)
          finally have ?thesis
            using \<open>signal_of (def A) \<tau> A i = def A\<close> \<open>signal_of (def B) \<tau> B i = def B\<close> by auto }
        ultimately have ?thesis
          by auto }
      ultimately show ?thesis
        by auto
    qed
  qed
next
  case False
  obtain \<tau>' t' \<sigma>' \<gamma>' where "init' 0 def {} 0 def nand4 \<tau> \<tau>'" and "next_time  0 \<tau>' = t'" and "next_state 0 \<tau>' def = \<sigma>'" and "next_event 0 \<tau>' def = \<gamma>'"
    using bsim[OF assms(1)] by meson
  have  bigstep: "Suc i, t', \<sigma>', \<gamma>', 0, def \<turnstile> <nand4, \<tau>'(t' := 0)> \<leadsto> res"
    using bsim[OF assms(1)] 
    by (metis \<open>init' 0 def {} 0 def nand4 \<tau> \<tau>'\<close> \<open>next_event 0 \<tau>' def = \<gamma>'\<close> \<open>next_state 0 \<tau>' def = \<sigma>'\<close> \<open>next_time 0 \<tau>' = t'\<close> assms(1) bsimulate_obt_big_step)
  have trans_removal: "\<And>n. n < t' \<Longrightarrow> (\<tau>'(t' := 0)) n = 0"
    using \<open>next_time 0 \<tau>' = t'\<close> next_time_at_least2 by auto
  have "\<tau> \<noteq> 0"
    using False by auto
  have "0 , def , {} , 0, def  \<turnstile> <Bassign_trans C (Bnand (Bsig A) (Bsig B)) 0 , \<tau>> \<longrightarrow>\<^sub>s \<tau>'"
    using init'_cases(1)[OF \<open>init' 0 def {} 0 def nand4 \<tau> \<tau>'\<close>[unfolded nand4_def]] by auto
  then obtain x where "0 , def , {} , 0, def  \<turnstile> Bnand (Bsig A) (Bsig B) \<longrightarrow>\<^sub>b x" and "trans_post_raw C x (def C) \<tau> 0 0 = \<tau>'"
    using seq_cases_trans[OF \<open>0 , def , {} , 0, def  \<turnstile> <Bassign_trans C (Bnand (Bsig A) (Bsig B)) 0 , \<tau>> \<longrightarrow>\<^sub>s \<tau>'\<close>] by blast
  hence "x = Bv (\<not> (bval_of (def A) \<and> bval_of (def B)))"
    by (smt assms(3) assms(4) assms(5) beval_cases(1) beval_cases(9) bexp_wt_cases(4)
    bexp_wt_cases_slice(2) conc_wt_cases(1) nand4_def seq_wt_cases(4) styping_def ty.simps(3)
    type_of.simps(2) val.sel(1))
  hence \<tau>'_def: "\<tau>' = trans_post_raw C (Bv (\<not> (bval_of (def A) \<and> bval_of (def B)))) (def C) \<tau> 0 0"
    using \<open>trans_post_raw C x (def C) \<tau> 0 0 = \<tau>'\<close> by blast
  have "\<tau>' \<noteq> 0"
  proof (rule ccontr)
    assume "\<not> \<tau>' \<noteq> 0" hence "\<tau>' = 0" by auto
    have "to_trans_raw_sig \<tau>' A = to_trans_raw_sig \<tau> A"
      unfolding \<tau>'_def to_trans_raw_sig_def trans_post_raw_def comp_def
    proof -
      have "\<forall>n. (if ((0::nat) < 0 + 0 \<longrightarrow> to_signal (def C) (\<lambda>s n. \<tau> n s) C (0 + 0 - 1) \<noteq> Bv (\<not> bval_of (def A) \<or> \<not> bval_of (def B))) \<and> (\<not> (0::nat) < 0 + 0 \<longrightarrow> def C \<noteq> Bv (\<not> bval_of (def A) \<or> \<not> bval_of (def B))) then post_raw C (Bv (\<not> bval_of (def A) \<or> \<not> bval_of (def B))) \<tau> (0 + 0) else preempt_raw C \<tau> (0 + 0)) n A = \<tau> n A"
        by (simp add: post_raw_def preempt_raw_def)
      then show "(\<lambda>n. (if if (0::nat) < 0 + 0 then to_signal (def C) (\<lambda>s n. \<tau> n s) C (0 + 0 - 1) \<noteq> Bv (\<not> (bval_of (def A) \<and> bval_of (def B))) else def C \<noteq> Bv (\<not> (bval_of (def A) \<and> bval_of (def B))) then post_raw C (Bv (\<not> (bval_of (def A) \<and> bval_of (def B)))) \<tau> (0 + 0) else preempt_raw C \<tau> (0 + 0)) n A) = (\<lambda>n. \<tau> n A)"
        by presburger
    qed
    hence "to_trans_raw_sig \<tau> A = 0"
      using \<open>\<tau>' = 0\<close>  by (simp add: to_trans_raw_sig_def zero_fun_def)
    hence "inf_time (to_trans_raw_sig \<tau>) A i = None"
      by (metis domIff inf_time_none_iff zero_map)
    have "to_trans_raw_sig \<tau>' B = to_trans_raw_sig \<tau> B"
      unfolding \<tau>'_def to_trans_raw_sig_def trans_post_raw_def comp_def 
    proof -
      { fix nn :: nat
        have "post_raw C (Bv (\<not> bval_of (def A) \<or> \<not> bval_of (def B))) \<tau> nn nn B = \<tau> nn B \<and> preempt_raw C \<tau> nn nn B = \<tau> nn B"
          by (simp add: post_raw_def preempt_raw_def)
        moreover
        { assume "0 + 0 \<noteq> nn"
          have "(0 + 0 \<noteq> nn \<and> \<not> 0 + 0 < nn) \<and> preempt_raw C \<tau> (0 + 0) nn B = \<tau> nn B \<or> (if ((0::nat) < 0 + 0 \<longrightarrow> to_signal (def C) (\<lambda>s n. \<tau> n s) C (0 + 0 - 1) \<noteq> Bv (\<not> bval_of (def A) \<or> \<not> bval_of (def B))) \<and> (\<not> (0::nat) < 0 + 0 \<longrightarrow> def C \<noteq> Bv (\<not> bval_of (def A) \<or> \<not> bval_of (def B))) then post_raw C (Bv (\<not> bval_of (def A) \<or> \<not> bval_of (def B))) \<tau> (0 + 0) else preempt_raw C \<tau> (0 + 0)) nn B = \<tau> nn B"
            by (simp add: post_raw_def preempt_raw_def)
          then have "(if ((0::nat) < 0 + 0 \<longrightarrow> to_signal (def C) (\<lambda>s n. \<tau> n s) C (0 + 0 - 1) \<noteq> Bv (\<not> bval_of (def A) \<or> \<not> bval_of (def B))) \<and> (\<not> (0::nat) < 0 + 0 \<longrightarrow> def C \<noteq> Bv (\<not> bval_of (def A) \<or> \<not> bval_of (def B))) then post_raw C (Bv (\<not> bval_of (def A) \<or> \<not> bval_of (def B))) \<tau> (0 + 0) else preempt_raw C \<tau> (0 + 0)) nn B = \<tau> nn B"
            by linarith }
        ultimately have "(if ((0::nat) < 0 + 0 \<longrightarrow> to_signal (def C) (\<lambda>s n. \<tau> n s) C (0 + 0 - 1) \<noteq> Bv (\<not> bval_of (def A) \<or> \<not> bval_of (def B))) \<and> (\<not> (0::nat) < 0 + 0 \<longrightarrow> def C \<noteq> Bv (\<not> bval_of (def A) \<or> \<not> bval_of (def B))) then post_raw C (Bv (\<not> bval_of (def A) \<or> \<not> bval_of (def B))) \<tau> (0 + 0) else preempt_raw C \<tau> (0 + 0)) nn B = \<tau> nn B"
          by force }
      then show "(\<lambda>n. (if if (0::nat) < 0 + 0 then to_signal (def C) (\<lambda>s n. \<tau> n s) C (0 + 0 - 1) \<noteq> Bv (\<not> (bval_of (def A) \<and> bval_of (def B))) else def C \<noteq> Bv (\<not> (bval_of (def A) \<and> bval_of (def B))) then post_raw C (Bv (\<not> (bval_of (def A) \<and> bval_of (def B)))) \<tau> (0 + 0) else preempt_raw C \<tau> (0 + 0)) n B) = (\<lambda>n. \<tau> n B)"
        by presburger
    qed
    hence "to_trans_raw_sig \<tau> B = 0"
      using \<open>\<tau>' = 0\<close>  by (simp add: to_trans_raw_sig_def zero_fun_def)
    hence "inf_time (to_trans_raw_sig \<tau>) B i = None"
      by (metis domIff inf_time_none_iff zero_map)
    with False show False
      by (simp add: \<open>inf_time (to_trans_raw_sig \<tau>) A i = None\<close>)
  qed
  have "inf_time (to_trans_raw_sig \<tau>) A i \<noteq> None \<or> inf_time (to_trans_raw_sig \<tau>) B i \<noteq> None"
    using False by auto
  then consider (both) "inf_time (to_trans_raw_sig \<tau>) A i \<noteq> None \<and> inf_time (to_trans_raw_sig \<tau>) B i \<noteq> None " 
    | (either) "inf_time (to_trans_raw_sig \<tau>) A i \<noteq> None \<and> inf_time (to_trans_raw_sig \<tau>) B i = None \<or> 
       inf_time (to_trans_raw_sig \<tau>) A i = None \<and> inf_time (to_trans_raw_sig \<tau>) B i \<noteq> None"
    by linarith
  then show ?thesis 
  proof (cases)
    case both
    then obtain time1 time2 time where "inf_time (to_trans_raw_sig \<tau>) A i = Some time1" and "inf_time (to_trans_raw_sig \<tau>) B i = Some time2"
        and "time = max time1 time2"
      by blast
    have "next_time 0 \<tau>' \<le> time"
    proof -
      have "next_time 0 \<tau>' = (LEAST n. dom (\<tau>' n) \<noteq> {})"
        unfolding next_time_def using \<open>\<tau>' \<noteq> 0\<close> by auto
      have "\<exists>n. dom (\<tau>' n) \<noteq> {}"
        using \<open>\<tau>' \<noteq> 0\<close> unfolding dom_def zero_fun_def zero_option_def 
        by fastforce
      have "inf_time (to_trans_raw_sig \<tau>) A i = inf_time (to_trans_raw_sig \<tau>') A i"
        using \<open>trans_post_raw C x (def C) \<tau> 0 0 = \<tau>'\<close> inf_time_trans_post by fastforce
      hence "dom (\<tau>' time1) \<noteq> {}"
        using \<open>inf_time (to_trans_raw_sig \<tau>) A i  = Some time1\<close> unfolding dom_def 
      proof -
        have "\<exists>s. to_trans_raw_sig \<tau>' s time1 \<noteq> None"
          by (metis Femto_VHDL_raw.keys_def \<open>inf_time (to_trans_raw_sig \<tau>) A i = Some time1\<close> \<open>inf_time (to_trans_raw_sig \<tau>) A i = inf_time (to_trans_raw_sig \<tau>') A i\<close> domIff dom_def inf_time_some_exists zero_option_def)
        then show "{s. \<tau>' time1 s \<noteq> None} \<noteq> {}"
          by (simp add: to_trans_raw_sig_def)
      qed
      hence "(LEAST n. dom (\<tau>' n) \<noteq> {}) \<le> time1"
        using Least_le by auto
      also have "... \<le> time"
        unfolding \<open>time = max time1 time2\<close> by auto
      finally show "next_time 0 \<tau>' \<le> time"
        using \<open>next_time 0 \<tau>' = (LEAST n. dom (\<tau>' n) \<noteq> {})\<close> by linarith
    qed
    have "time < Suc i"
      unfolding \<open>time = max time1 time2\<close> 
      using \<open>inf_time (to_trans_raw_sig \<tau>) A i = Some time1\<close> \<open>inf_time (to_trans_raw_sig \<tau>) B i = Some time2\<close>
      inf_time_at_most by fastforce
    have "\<exists>res'. time, t' , \<sigma>' , \<gamma>' , 0, def \<turnstile> <nand4 , \<tau>'(t' := 0)> \<leadsto> res' \<and> Suc i, time , get_state res' , get_beh' res' , get_beh res', def \<turnstile> <nand4 , get_trans res'> \<leadsto> res"
      using split_b_simulate_fin[OF bigstep \<open>next_time 0 \<tau>' \<le>time\<close>[unfolded \<open>next_time 0 \<tau>' = t'\<close>] _ trans_removal conc_stmt_wf_nand4]  \<open>time < Suc i\<close>
      by (meson less_or_eq_imp_le zero_fun_def)
    then obtain res' where bigstep2_pre: "time, t' , \<sigma>' , \<gamma>' , 0, def \<turnstile> <nand4 , \<tau>'(t' := 0)> \<leadsto> res'"
      and bigstep2: "Suc i, time , get_state res' , get_beh' res' , get_beh res', def \<turnstile> <nand4 , get_trans res'> \<leadsto> res"
      by auto
    have "A \<notin> set (signals_from nand4)" and "B \<notin> set (signals_from nand4)"
      unfolding nand4_def by auto
    have "t' < time \<or> t' = time"
      using bau bigstep2_pre by blast
    moreover 
    { assume "t' < time"
      moreover have "\<tau>' time A = \<tau> time A" and "\<tau>' time B = \<tau> time B"
        unfolding \<tau>'_def trans_post_raw_def post_raw_def preempt_raw_def by auto
      moreover have "\<tau> time A \<noteq> 0 \<or> \<tau> time B \<noteq> 0"
        using \<open>inf_time (to_trans_raw_sig \<tau>) A i = Some time1\<close> \<open>inf_time (to_trans_raw_sig \<tau>) B i = Some time2\<close> \<open>time = max time1 time2\<close>
      proof -
        have f1: "\<And>n. Some time2 \<noteq> Some n \<or> to_trans_raw_sig \<tau> B n \<noteq> 0"
          using Femto_VHDL_raw.keys_def \<open>inf_time (to_trans_raw_sig \<tau>) B i = Some time2\<close> inf_time_some_exists by fastforce
        have "\<And>n. Some time1 \<noteq> Some n \<or> to_trans_raw_sig \<tau> A n \<noteq> 0"
          using Femto_VHDL_raw.keys_def \<open>inf_time (to_trans_raw_sig \<tau>) A i = Some time1\<close> inf_time_some_exists by fastforce
        then show ?thesis
          using f1 by (metis (no_types) \<open>time = max time1 time2\<close> max_def to_trans_raw_sig_def)
      qed
      ultimately have "(\<tau>'(t' := 0)) time A \<noteq> 0 \<or> (\<tau>'(t' := 0)) time B \<noteq> 0"
        by auto
      then obtain sigAB where "(\<tau>'(t' := 0)) time sigAB \<noteq> 0" and "sigAB = A \<or> sigAB = B"
        by blast
      hence "sigAB \<notin> set (signals_from nand4)"
        unfolding nand4_def by auto
      have "non_stuttering (to_trans_raw_sig \<tau>') def sigAB"
        using init'_preserves_non_stuttering[OF `init' 0 def {} 0 def nand4 \<tau> \<tau>'` _ _ conc_stmt_wf_nand4] assms(7)
        by blast
      hence "non_stuttering (to_trans_raw_sig (\<tau>'(t' := 0))) \<sigma>' sigAB"
        using non_stuttering_next \<open>next_state 0 \<tau>' def = \<sigma>'\<close> \<open>next_time 0 \<tau>' = t'\<close> by fastforce
      hence "get_event res' \<noteq>  {}"
        using get_event_never_empty'[OF bigstep2_pre \<open>sigAB \<notin> set (signals_from nand4)\<close> ` (\<tau>'(t' := 0)) time sigAB \<noteq> 0 ` _ _ trans_removal conc_stmt_wf_nand4]
        using \<open>t' < time\<close> by blast 
      have "\<not> disjnt {A, B} (get_event res')"
        using get_event_never_empty[OF bigstep2_pre \<open>sigAB \<notin> set (signals_from nand4)\<close> ` (\<tau>'(t' := 0)) time sigAB \<noteq> 0 ` _ _ trans_removal conc_stmt_wf_nand4]
        using \<open>t' < time\<close> \<open>non_stuttering (to_trans_raw_sig (\<tau>'(t' := 0))) \<sigma>' sigAB\<close> \<open>sigAB = A \<or> sigAB = B\<close> by fastforce
      hence "get_event res' \<noteq>  {} \<and> \<not> disjnt {A, B} (get_event res')"
        by auto }
    moreover 
    { assume "t' = time"
      hence "res' = (time, \<sigma>', \<gamma>', 0, \<tau>'(t' := 0))"
        using bau[OF bigstep2_pre] by auto
      hence "get_event res' = \<gamma>'"
        by auto
      also have "... = next_event 0 \<tau>' def"
        using \<open>next_event 0 \<tau>' def = \<gamma>'\<close> by auto
      also have "... = {sig. def sig \<noteq> next_state 0 \<tau>' def sig} "
        unfolding next_event_alt_def by auto
      also have "... \<noteq> {}"
      proof -
        have "\<tau>' time A = \<tau> time A" and "\<tau>' time B = \<tau> time B"
          unfolding \<tau>'_def trans_post_raw_def post_raw_def preempt_raw_def by auto
        moreover have "\<tau> time A \<noteq> 0 \<or> \<tau> time B \<noteq> 0"
          using \<open>inf_time (to_trans_raw_sig \<tau>) A i = Some time1\<close> \<open>inf_time (to_trans_raw_sig \<tau>) B i = Some time2\<close> \<open>time = max time1 time2\<close>
        proof -
          have f1: "\<And>n. Some time2 \<noteq> Some n \<or> to_trans_raw_sig \<tau> B n \<noteq> 0"
            using Femto_VHDL_raw.keys_def \<open>inf_time (to_trans_raw_sig \<tau>) B i = Some time2\<close> inf_time_some_exists by fastforce
          have "\<And>n. Some time1 \<noteq> Some n \<or> to_trans_raw_sig \<tau> A n \<noteq> 0"
            using Femto_VHDL_raw.keys_def \<open>inf_time (to_trans_raw_sig \<tau>) A i = Some time1\<close> inf_time_some_exists by fastforce
          then show ?thesis
            using f1 by (metis (no_types) \<open>time = max time1 time2\<close> max_def to_trans_raw_sig_def)
        qed
        ultimately have "\<tau>' time A \<noteq> 0 \<or> \<tau>' time B \<noteq> 0"
          by auto
        then obtain sigAB where "\<tau>' time sigAB \<noteq> 0" and "sigAB = A \<or> sigAB = B"
          by auto
        moreover have "\<tau>' time sigAB = \<tau> time sigAB"
          using \<open>\<tau>' time A = \<tau> time A\<close> \<open>\<tau>' time B = \<tau> time B\<close> calculation(2) by blast
        moreover have  "Femto_VHDL_raw.keys (to_trans_raw_sig \<tau> sigAB) \<noteq> {}"
          using \<open>inf_time (to_trans_raw_sig \<tau>) A i = Some time1\<close> \<open>inf_time (to_trans_raw_sig \<tau>) B i
          = Some time2\<close> calculation(2) inf_time_some_exists by force
        moreover have *: "(LEAST k. k \<in> Femto_VHDL_raw.keys (to_trans_raw_sig \<tau> sigAB)) = time"
        proof (rule Least_equality)
          show " time \<in> Femto_VHDL_raw.keys (to_trans_raw_sig \<tau> sigAB)"
            by (metis Femto_VHDL_raw.keys_def calculation(1) calculation(3) domIff dom_def to_trans_raw_sig_def zero_option_def)
        next
          { fix y 
            assume "y < time"
            assume "y \<in> Femto_VHDL_raw.keys (to_trans_raw_sig \<tau> sigAB)"
            hence "\<tau> y sigAB \<noteq> 0"
              unfolding Femto_VHDL_raw.keys_def to_trans_raw_sig_def by auto
            hence "\<tau>' y sigAB \<noteq> 0"
              by (metis \<open>trans_post_raw C x (def C) \<tau> 0 0 = \<tau>'\<close> calculation(2) sig.distinct(3) sig.distinct(5) to_trans_raw_sig_def trans_post_raw_diff_sig)
            with `y < time` have False
              unfolding `t' = time`[THEN sym] `next_time  0 \<tau>' = t'`[THEN sym] 
              by (simp add: next_time_at_least2 zero_fun_def) }
          thus "\<And>y. y \<in> Femto_VHDL_raw.keys (to_trans_raw_sig \<tau> sigAB) \<Longrightarrow> time \<le> y"
            using not_less by blast
        qed
        moreover have "the (to_trans_raw_sig \<tau> sigAB (LEAST k. k \<in> Femto_VHDL_raw.keys (to_trans_raw_sig \<tau> sigAB))) = next_state 0 \<tau>' def sigAB"
          unfolding * next_state_def 
          by (metis \<open>next_time 0 \<tau>' = t'\<close> \<open>t' = time\<close> calculation(1) calculation(3) comp_apply domIff override_on_apply_in to_trans_raw_sig_def zero_option_def) 
        ultimately show ?thesis
          using assms(7)[unfolded non_stuttering_def] by auto
      qed
      finally have "get_event res' \<noteq>  {}"
        by auto
      have "\<not> disjnt {A, B} (get_event res')"
      proof -
        have "\<tau>' time A = \<tau> time A" and "\<tau>' time B = \<tau> time B"
          unfolding \<tau>'_def trans_post_raw_def post_raw_def preempt_raw_def by auto
        moreover have "\<tau> time A \<noteq> 0 \<or> \<tau> time B \<noteq> 0"
          using \<open>inf_time (to_trans_raw_sig \<tau>) A i = Some time1\<close> \<open>inf_time (to_trans_raw_sig \<tau>) B i = Some time2\<close> \<open>time = max time1 time2\<close>
        proof -
          have f1: "\<And>n. Some time2 \<noteq> Some n \<or> to_trans_raw_sig \<tau> B n \<noteq> 0"
            using Femto_VHDL_raw.keys_def \<open>inf_time (to_trans_raw_sig \<tau>) B i = Some time2\<close> inf_time_some_exists by fastforce
          have "\<And>n. Some time1 \<noteq> Some n \<or> to_trans_raw_sig \<tau> A n \<noteq> 0"
            using Femto_VHDL_raw.keys_def \<open>inf_time (to_trans_raw_sig \<tau>) A i = Some time1\<close> inf_time_some_exists by fastforce
          then show ?thesis
            using f1 by (metis (no_types) \<open>time = max time1 time2\<close> max_def to_trans_raw_sig_def)
        qed
        ultimately have "\<tau>' time A \<noteq> 0 \<or> \<tau>' time B \<noteq> 0"
          by auto
        then obtain sigAB where "\<tau>' time sigAB \<noteq> 0" and "sigAB = A \<or> sigAB = B"
          by auto
        moreover have "\<tau>' time sigAB = \<tau> time sigAB"
          using \<open>\<tau>' time A = \<tau> time A\<close> \<open>\<tau>' time B = \<tau> time B\<close> calculation(2) by blast
        moreover have  "Femto_VHDL_raw.keys (to_trans_raw_sig \<tau> sigAB) \<noteq> {}"
          using \<open>inf_time (to_trans_raw_sig \<tau>) A i = Some time1\<close> \<open>inf_time (to_trans_raw_sig \<tau>) B i
          = Some time2\<close> calculation(2) inf_time_some_exists by force
        moreover have *: "(LEAST k. k \<in> Femto_VHDL_raw.keys (to_trans_raw_sig \<tau> sigAB)) = time"
        proof (rule Least_equality)
          show " time \<in> Femto_VHDL_raw.keys (to_trans_raw_sig \<tau> sigAB)"
            by (metis Femto_VHDL_raw.keys_def calculation(1) calculation(3) domIff dom_def to_trans_raw_sig_def zero_option_def)
        next
          { fix y 
            assume "y < time"
            assume "y \<in> Femto_VHDL_raw.keys (to_trans_raw_sig \<tau> sigAB)"
            hence "\<tau> y sigAB \<noteq> 0"
              unfolding Femto_VHDL_raw.keys_def to_trans_raw_sig_def by auto
            hence "\<tau>' y sigAB \<noteq> 0"
              by (metis \<open>trans_post_raw C x (def C) \<tau> 0 0 = \<tau>'\<close> calculation(2) sig.distinct(3) sig.distinct(5) to_trans_raw_sig_def trans_post_raw_diff_sig)
            with `y < time` have False
              unfolding `t' = time`[THEN sym] `next_time  0 \<tau>' = t'`[THEN sym] 
              by (simp add: next_time_at_least2 zero_fun_def) }
          thus "\<And>y. y \<in> Femto_VHDL_raw.keys (to_trans_raw_sig \<tau> sigAB) \<Longrightarrow> time \<le> y"
            using not_less by blast
        qed
        moreover have "the (to_trans_raw_sig \<tau> sigAB (LEAST k. k \<in> Femto_VHDL_raw.keys (to_trans_raw_sig \<tau> sigAB))) = next_state 0 \<tau>' def sigAB"
          unfolding * next_state_def 
          by (metis \<open>next_time 0 \<tau>' = t'\<close> \<open>t' = time\<close> calculation(1) calculation(3) comp_apply domIff override_on_apply_in to_trans_raw_sig_def zero_option_def) 
        ultimately show ?thesis
          by (metis (full_types) \<open>get_beh' res' = \<gamma>'\<close> \<open>next_event 0 \<tau>' def = \<gamma>'\<close> assms(7) disjnt_insert1 next_state_fixed_point non_stuttering_def)
      qed 
      hence "get_event res' \<noteq> {} \<and> \<not> disjnt {A, B} (get_event res')"
        using \<open>get_beh' res' \<noteq> {}\<close> by blast }
    ultimately have "get_event res' \<noteq> {} \<and> \<not> disjnt {A, B} (get_event res')"
      by auto
    hence " \<not> quiet (get_trans res') (get_event res')" and "\<not> disjnt {A, B} (get_event res')"
      by (simp add: quiet_def)+
    then obtain \<tau>_res where "time, get_state res', get_event res', get_beh res', def \<turnstile> <nand4, get_trans res'> \<longrightarrow>\<^sub>c \<tau>_res"
      using bau[OF bigstep2]  using \<open>time < Suc i\<close> by force
    have "next_time time \<tau>_res \<le> Suc i \<or> Suc i < next_time time \<tau>_res"
      by auto
    moreover
    { assume "Suc i < next_time time \<tau>_res"
      hence " res = (Suc i, get_state res', {}, Femto_VHDL_raw.add_to_beh2 (get_state res') (get_beh res') time def, \<tau>_res) "
        using bau[OF bigstep2] `\<not> quiet (get_trans res') (get_event res')` `time < Suc i` 
        by (smt \<open>time , get_state res' , get_beh' res' , get_beh res', def \<turnstile> <nand4 , get_trans
        res'> \<longrightarrow>\<^sub>c \<tau>_res\<close> b_conc_exec_deterministic less_irrefl_nat not_le)
      hence gb_res: "get_beh res =  Femto_VHDL_raw.add_to_beh2 (get_state res') (get_beh res') time def"
        by auto
      have "time \<le> i"
        using \<open>time < Suc i\<close> less_Suc_eq_le by blast
      have "\<forall>n>time. get_beh res' n C = 0"
        by (metis b_simulate_fin_preserves_hist bigstep2_pre trans_removal zero_fun_def)
      hence "signal_of (def C) (get_beh res) C i = get_state res' C"
        using signal_of_add_to_beh2'[OF `time \<le> i` ] unfolding gb_res by auto
      have "signal_of (def A) \<tau> A i  = signal_of (def A) \<tau>' A i"
        using init'_modifies_local_strongest[OF `init' 0 def {} 0 def nand4 \<tau> \<tau>'` `A \<notin> set (signals_from nand4)`]
        using \<open>trans_post_raw C x (def C) \<tau> 0 0 = \<tau>'\<close> signal_of_trans_post by fastforce
      also have "... = signal_of (\<sigma>' A) \<tau>' A i"
        by (metis \<open>inf_time (to_trans_raw_sig \<tau>) A i = Some time1\<close> \<open>trans_post_raw C x (def C) \<tau> 0 0 = \<tau>'\<close> comp_apply option.simps(5) sig.distinct(3) signal_of_trans_post to_signal_def)
      also have "... = signal_of (\<sigma>' A) (\<tau>'(t':=0)) A i"
        by (smt \<open>next_state 0 \<tau>' def = \<sigma>'\<close> \<open>next_time 0 \<tau>' = t'\<close> comp_apply next_state_def next_time_at_least2 override_on_apply_in signal_of_rem_curr_trans_at_t)
      also have "... = signal_of (get_state res' A) (get_trans res') A i"
        using bau_signal_of[OF bigstep2_pre `A \<notin> set (signals_from nand4)` `time \<le> i` trans_removal]
        by blast
      also have "... = get_state res' A"
        by (rule signal_of_def)
           (metis (no_types, lifting) Suc_lessD \<open>A \<notin> set (signals_from nand4)\<close> \<open>Suc i < next_time
           time \<tau>_res\<close> \<open>time , get_state res' , get_beh' res' , get_beh res', def \<turnstile> <nand4 ,
           get_trans res'> \<longrightarrow>\<^sub>c \<tau>_res\<close> antisym_conv2 b_conc_exec_modifies_local_strongest
           dual_order.strict_trans next_time_at_least2 zero_fun_def)
      finally have "signal_of (def A) \<tau> A i = get_state res' A"
        by auto
      have "signal_of (def B) \<tau> B i  = signal_of (def B) \<tau>' B i"
        using init'_modifies_local_strongest[OF `init' 0 def {} 0 def nand4 \<tau> \<tau>'` `B \<notin> set (signals_from nand4)`]
        using \<open>trans_post_raw C x (def C) \<tau> 0 0 = \<tau>'\<close> signal_of_trans_post by fastforce
      also have "... = signal_of (\<sigma>' B) \<tau>' B i"
        by (metis \<open>0 , def , {} , 0, def \<turnstile> <Bassign_trans C (Bnand (Bsig A) (Bsig B)) 0 , \<tau>> \<longrightarrow>\<^sub>s \<tau>'\<close>
        \<open>\<And>thesis. (\<And>time1 time2 time. \<lbrakk>inf_time (to_trans_raw_sig \<tau>) A i = Some time1; inf_time
        (to_trans_raw_sig \<tau>) B i = Some time2; time = max time1 time2\<rbrakk> \<Longrightarrow> thesis) \<Longrightarrow> thesis\<close> comp_def
        inf_time_trans_post option.simps(5) seq_cases_trans sig.distinct(5) to_signal_def)
      also have "... = signal_of (\<sigma>' B) (\<tau>'(t':=0)) B i"
        by (smt \<open>next_state 0 \<tau>' def = \<sigma>'\<close> \<open>next_time 0 \<tau>' = t'\<close> comp_apply next_state_def next_time_at_least2 override_on_apply_in signal_of_rem_curr_trans_at_t)
      also have "... = signal_of (get_state res' B) (get_trans res') B i"
        using bau_signal_of[OF bigstep2_pre `B \<notin> set (signals_from nand4)` `time \<le> i` trans_removal]
        by blast
      also have "... = get_state res' B"
        by (rule signal_of_def)
           (metis (no_types, lifting) Suc_lessD \<open>B \<notin> set (signals_from nand4)\<close> \<open>Suc i < next_time
           time \<tau>_res\<close> \<open>time , get_state res' , get_beh' res' , get_beh res', def \<turnstile> <nand4 ,
           get_trans res'> \<longrightarrow>\<^sub>c \<tau>_res\<close> antisym_conv2 b_conc_exec_modifies_local_strongest
           dual_order.strict_trans next_time_at_least2 zero_fun_def)
      finally have "signal_of (def B) \<tau> B i = get_state res' B"
        by auto
      have "time , get_state res' , get_event res' , get_beh res', def  \<turnstile> <Bassign_trans C (Bnand (Bsig A) (Bsig B)) 0 , get_trans res'> \<longrightarrow>\<^sub>s \<tau>_res"
        using conc_cases(1)[OF `time, get_state res', get_event res', get_beh res', def \<turnstile> <nand4, get_trans res'> \<longrightarrow>\<^sub>c \<tau>_res`[unfolded nand4_def]]
        `\<not> disjnt {A, B} (get_event res')` by auto
      obtain x' where " time , get_state res' , get_beh' res' , get_beh res', def  \<turnstile> Bnand (Bsig A) (Bsig B) \<longrightarrow>\<^sub>b x'" and 
        \<tau>_res_def: " trans_post_raw C x' (get_state res' C) (get_trans res') time 0 = \<tau>_res"
        using seq_cases_trans[OF `time , get_state res' , get_event res' , get_beh res', def  \<turnstile> <Bassign_trans C (Bnand (Bsig A) (Bsig B)) 0 , get_trans res'> \<longrightarrow>\<^sub>s \<tau>_res`]
        by blast
      have "time , get_state res' , get_beh' res' , get_beh res', def  \<turnstile> Bsig A \<longrightarrow>\<^sub>b Bv (bval_of (get_state res' A))"
        by (smt \<open>0 , def , {} , 0, def \<turnstile> Bnand (Bsig A) (Bsig B) \<longrightarrow>\<^sub>b x\<close> \<open>signal_of (def A) \<tau> A i =
        get_state res' A\<close> \<open>x = Bv (\<not> (bval_of (def A) \<and> bval_of (def B)))\<close> assms(4) assms(6)
        beval_cases(1) beval_cases(9) beval_raw.intros(1) signal_of_preserve_well_typedness
        styping_def ty.simps(3) type_of.simps(1) type_of.simps(2) val.exhaust_sel)
      moreover have "time , get_state res' , get_beh' res' , get_beh res', def  \<turnstile> Bsig B \<longrightarrow>\<^sub>b Bv (bval_of (get_state res' B))"
        by (smt \<open>time , get_state res' , get_beh' res' , get_beh res', def \<turnstile> Bnand (Bsig A) (Bsig B)
        \<longrightarrow>\<^sub>b x'\<close> \<open>time , get_state res' , get_beh' res' , get_beh res', def \<turnstile> Bsig A \<longrightarrow>\<^sub>b Bv (bval_of
        (get_state res' A))\<close> beval_cases(9) beval_raw.intros(1) beval_raw_deterministic
        val.distinct(1) val.exhaust_sel)
      ultimately have "x' = Bv (\<not> (bval_of (get_state res' A) \<and> bval_of (get_state res' B)))"
        using beval_cases(9)[OF `time , get_state res' , get_beh' res' , get_beh res', def  \<turnstile> Bnand (Bsig A) (Bsig B) \<longrightarrow>\<^sub>b x'`]
        by (smt beval_cases(1) val.distinct(1))
      have "\<not> post_necessary_raw 0 (get_trans res') time C x' (get_state res' C)"
      proof (rule ccontr)
        assume "\<not> \<not> post_necessary_raw 0 (get_trans res') time C x' (get_state res' C)"
        hence "post_necessary_raw 0 (get_trans res') time C x' (get_state res' C)"
          by auto
        hence "\<tau>_res time C = post_raw C x' (get_trans res') (time + 0) time C"
          unfolding \<tau>_res_def[THEN sym] trans_post_raw_def by auto
        hence "next_time time \<tau>_res = time"
          by (metis (no_types, lifting) \<open>Suc i < next_time time \<tau>_res\<close> \<open>time < Suc i\<close>
          add.right_neutral dual_order.strict_trans fun_upd_same next_time_at_least2
          option.distinct(1) post_raw_def zero_fun_def zero_option_def)
        thus "False"
          using `Suc i < next_time time \<tau>_res`  using \<open>time < Suc i\<close> by linarith
      qed
      moreover have "\<not> (\<exists>i\<le>time + 0 - 1. get_trans res' i C = Some x')"
        using b_simulate_fin_preserve_trans_removal[OF bigstep2_pre trans_removal] 
        by (metis (no_types, hide_lams) Suc_diff_1 \<open>t' < time \<or> t' = time\<close> add.right_neutral
        b_simulate_fin.intros(4) b_simulate_fin_deterministic bigstep2_pre comp_eq_dest_lhs
        diff_le_self fun_upd_same le_imp_less_Suc not_gr_zero not_le not_less_zero
        option.distinct(1) snd_conv zero_fun_def zero_option_def)
      ultimately have "x' = get_state res' C"
        unfolding post_necessary_raw_correctness by blast
      hence "bval_of (get_state res' C) \<longleftrightarrow> \<not> (bval_of (get_state res' A) \<and> bval_of (get_state res' B))"
        using `x' = Bv (\<not> (bval_of (get_state res' A) \<and> bval_of (get_state res' B)))`
        using val.sel(1) by presburger
      hence ?thesis
        using `signal_of (def A) \<tau> A i = get_state res' A` `signal_of (def B) \<tau> B i = get_state res' B`
        `signal_of (def C) (get_beh res) C i = get_state res' C` by auto }
    moreover
    { assume "next_time time \<tau>_res = Suc i"
      hence bigstep3: "Suc i, next_time time \<tau>_res , next_state time \<tau>_res (get_state res') , next_event time \<tau>_res (get_state res') , Femto_VHDL_raw.add_to_beh2 (get_state res') (get_beh res') time def, def \<turnstile> <nand4 , \<tau>_res (next_time time \<tau>_res := 0)> \<leadsto> res"
        using bau[OF bigstep2] 
        by (smt \<open>\<not> quiet (get_trans res') (get_beh' res')\<close> \<open>time , get_state res' , get_beh' res' ,
        get_beh res', def \<turnstile> <nand4 , get_trans res'> \<longrightarrow>\<^sub>c \<tau>_res\<close> \<open>time < Suc i\<close> bigstep2
        calculation(1) case_bau less_irrefl_nat)
      have "res = (Suc i, next_state time \<tau>_res (get_state res'), next_event time \<tau>_res (get_state res'), Femto_VHDL_raw.add_to_beh2 (get_state res') (get_beh res') time def, \<tau>_res (next_time time \<tau>_res := 0))"
        using bau[OF bigstep3] `next_time time \<tau>_res = Suc i` by auto
      hence gb_res: "get_beh res = Femto_VHDL_raw.add_to_beh2 (get_state res') (get_beh res') time def"
        by auto
      have "time \<le> i"
        using \<open>time < Suc i\<close> less_Suc_eq_le by blast
      have "\<forall>n>time. get_beh res' n C = 0"
        by (metis b_simulate_fin_preserves_hist bigstep2_pre trans_removal zero_fun_def)
      hence "signal_of (def C) (get_beh res) C i = get_state res' C"
        using signal_of_add_to_beh2'[OF `time \<le> i` ] unfolding gb_res by auto
      have "signal_of (def A) \<tau> A i  = signal_of (def A) \<tau>' A i"
        using init'_modifies_local_strongest[OF `init' 0 def {} 0 def nand4 \<tau> \<tau>'` `A \<notin> set (signals_from nand4)`]
        using \<open>trans_post_raw C x (def C) \<tau> 0 0 = \<tau>'\<close> signal_of_trans_post by fastforce
      also have "... = signal_of (\<sigma>' A) \<tau>' A i"
        by (metis \<open>inf_time (to_trans_raw_sig \<tau>) A i = Some time1\<close> \<open>trans_post_raw C x (def C) \<tau> 0 0 = \<tau>'\<close> comp_apply option.simps(5) sig.distinct(3) signal_of_trans_post to_signal_def)
      also have "... = signal_of (\<sigma>' A) (\<tau>'(t':=0)) A i"
        by (smt \<open>next_state 0 \<tau>' def = \<sigma>'\<close> \<open>next_time 0 \<tau>' = t'\<close> comp_apply next_state_def next_time_at_least2 override_on_apply_in signal_of_rem_curr_trans_at_t)
      also have "... = signal_of (get_state res' A) (get_trans res') A i"
        using bau_signal_of[OF bigstep2_pre `A \<notin> set (signals_from nand4)` `time \<le> i` trans_removal]
        by blast
      also have "... = get_state res' A"
        by (metis (no_types, lifting) \<open>A \<notin> set (signals_from nand4)\<close> \<open>next_time time \<tau>_res = Suc i\<close> \<open>time , get_state res' , get_beh' res' , get_beh res', def \<turnstile> <nand4 , get_trans res'> \<longrightarrow>\<^sub>c \<tau>_res\<close> b_conc_exec_modifies_local_strongest dual_order.strict_trans2 lessI next_time_at_least2 signal_of_def zero_fun_def)
      finally have "signal_of (def A) \<tau> A i = get_state res' A"
        by auto
      have "signal_of (def B) \<tau> B i  = signal_of (def B) \<tau>' B i"
        using init'_modifies_local_strongest[OF `init' 0 def {} 0 def nand4 \<tau> \<tau>'` `B \<notin> set (signals_from nand4)`]
        using \<open>trans_post_raw C x (def C) \<tau> 0 0 = \<tau>'\<close> signal_of_trans_post by fastforce
      also have "... = signal_of (\<sigma>' B) \<tau>' B i"
        by (metis \<open>0 , def , {} , 0, def \<turnstile> <Bassign_trans C (Bnand (Bsig A) (Bsig B)) 0 , \<tau>> \<longrightarrow>\<^sub>s \<tau>'\<close>
        \<open>\<And>thesis. (\<And>time1 time2 time. \<lbrakk>inf_time (to_trans_raw_sig \<tau>) A i = Some time1; inf_time
        (to_trans_raw_sig \<tau>) B i = Some time2; time = max time1 time2\<rbrakk> \<Longrightarrow> thesis) \<Longrightarrow> thesis\<close> comp_def
        inf_time_trans_post option.simps(5) seq_cases_trans sig.distinct(5) to_signal_def)
      also have "... = signal_of (\<sigma>' B) (\<tau>'(t':=0)) B i"
        by (smt \<open>next_state 0 \<tau>' def = \<sigma>'\<close> \<open>next_time 0 \<tau>' = t'\<close> comp_apply next_state_def next_time_at_least2 override_on_apply_in signal_of_rem_curr_trans_at_t)
      also have "... = signal_of (get_state res' B) (get_trans res') B i"
        using bau_signal_of[OF bigstep2_pre `B \<notin> set (signals_from nand4)` `time \<le> i` trans_removal]
        by blast
      also have "... = get_state res' B"
        by (metis (no_types, lifting) \<open>B \<notin> set (signals_from nand4)\<close> \<open>next_time time \<tau>_res = Suc i\<close> \<open>time , get_state res' , get_beh' res' , get_beh res', def \<turnstile> <nand4 , get_trans res'> \<longrightarrow>\<^sub>c \<tau>_res\<close> b_conc_exec_modifies_local_strongest dual_order.strict_trans2 lessI next_time_at_least2 signal_of_def zero_fun_def)
      finally have "signal_of (def B) \<tau> B i = get_state res' B"
        by auto
      have "time , get_state res' , get_event res' , get_beh res', def  \<turnstile> <Bassign_trans C (Bnand (Bsig A) (Bsig B)) 0 , get_trans res'> \<longrightarrow>\<^sub>s \<tau>_res"
        using conc_cases(1)[OF `time, get_state res', get_event res', get_beh res', def \<turnstile> <nand4, get_trans res'> \<longrightarrow>\<^sub>c \<tau>_res`[unfolded nand4_def]]
        `\<not> disjnt {A, B} (get_event res')` by auto
      obtain x' where " time , get_state res' , get_beh' res' , get_beh res', def  \<turnstile> Bnand (Bsig A) (Bsig B) \<longrightarrow>\<^sub>b x'" and 
        \<tau>_res_def: " trans_post_raw C x' (get_state res' C) (get_trans res') time 0 = \<tau>_res"
        using seq_cases_trans[OF `time , get_state res' , get_event res' , get_beh res', def  \<turnstile> <Bassign_trans C (Bnand (Bsig A) (Bsig B)) 0 , get_trans res'> \<longrightarrow>\<^sub>s \<tau>_res`]
        by blast
      have "time , get_state res' , get_beh' res' , get_beh res', def  \<turnstile> Bsig A \<longrightarrow>\<^sub>b Bv (bval_of (get_state res' A))"
        by (smt \<open>0 , def , {} , 0, def \<turnstile> Bnand (Bsig A) (Bsig B) \<longrightarrow>\<^sub>b x\<close> \<open>signal_of (def A) \<tau> A i =
        get_state res' A\<close> \<open>x = Bv (\<not> (bval_of (def A) \<and> bval_of (def B)))\<close> assms(4) assms(6)
        beval_cases(1) beval_cases(9) beval_raw.intros(1) signal_of_preserve_well_typedness
        styping_def ty.simps(3) type_of.simps(1) type_of.simps(2) val.exhaust_sel)
      moreover have "time , get_state res' , get_beh' res' , get_beh res', def  \<turnstile> Bsig B \<longrightarrow>\<^sub>b Bv (bval_of (get_state res' B))"
        by (smt \<open>time , get_state res' , get_beh' res' , get_beh res', def \<turnstile> Bnand (Bsig A) (Bsig B)
        \<longrightarrow>\<^sub>b x'\<close> \<open>time , get_state res' , get_beh' res' , get_beh res', def \<turnstile> Bsig A \<longrightarrow>\<^sub>b Bv (bval_of
        (get_state res' A))\<close> beval_cases(9) beval_raw.intros(1) beval_raw_deterministic
        val.distinct(1) val.exhaust_sel)
      ultimately have "x' = Bv (\<not> (bval_of (get_state res' A) \<and> bval_of (get_state res' B)))"
        using beval_cases(9)[OF `time , get_state res' , get_beh' res' , get_beh res', def  \<turnstile> Bnand (Bsig A) (Bsig B) \<longrightarrow>\<^sub>b x'`]
        by (smt beval_cases(1) val.distinct(1))
      have "\<not> post_necessary_raw 0 (get_trans res') time C x' (get_state res' C)"
      proof (rule ccontr)
        assume "\<not> \<not> post_necessary_raw 0 (get_trans res') time C x' (get_state res' C)"
        hence "post_necessary_raw 0 (get_trans res') time C x' (get_state res' C)"
          by auto
        hence "\<tau>_res time C = post_raw C x' (get_trans res') (time + 0) time C"
          unfolding \<tau>_res_def[THEN sym] trans_post_raw_def by auto
        hence "next_time time \<tau>_res = time"
          by (metis (no_types, lifting) \<open> next_time time \<tau>_res = Suc i\<close> \<open>time < Suc i\<close>
          add.right_neutral dual_order.strict_trans fun_upd_same next_time_at_least2
          option.distinct(1) post_raw_def zero_fun_def zero_option_def)
        thus "False"
          using `next_time time \<tau>_res = Suc i`  using \<open>time < Suc i\<close> by linarith
      qed
      moreover have "\<not> (\<exists>i\<le>time + 0 - 1. get_trans res' i C = Some x')"
        using b_simulate_fin_preserve_trans_removal[OF bigstep2_pre trans_removal] 
        by (metis (no_types, hide_lams) Suc_diff_1 \<open>t' < time \<or> t' = time\<close> add.right_neutral
        b_simulate_fin.intros(4) b_simulate_fin_deterministic bigstep2_pre comp_eq_dest_lhs
        diff_le_self fun_upd_same le_imp_less_Suc not_gr_zero not_le not_less_zero
        option.distinct(1) snd_conv zero_fun_def zero_option_def)
      ultimately have "x' = get_state res' C"
        unfolding post_necessary_raw_correctness by blast
      hence "bval_of (get_state res' C) \<longleftrightarrow> \<not> (bval_of (get_state res' A) \<and> bval_of (get_state res' B))"
        using `x' = Bv (\<not> (bval_of (get_state res' A) \<and> bval_of (get_state res' B)))`
        using val.sel(1) by presburger
      hence ?thesis
        using `signal_of (def A) \<tau> A i = get_state res' A` `signal_of (def B) \<tau> B i = get_state res' B`
        `signal_of (def C) (get_beh res) C i = get_state res' C` by auto }
    moreover
    { assume "next_time time \<tau>_res < Suc i"
      hence bigstep3: "Suc i, next_time time \<tau>_res , next_state time \<tau>_res (get_state res') , next_event time \<tau>_res (get_state res') , Femto_VHDL_raw.add_to_beh2 (get_state res') (get_beh res') time def, def \<turnstile> <nand4 , \<tau>_res (next_time time \<tau>_res := 0)> \<leadsto> res"
        using bau[OF bigstep2] 
        by (smt \<open>\<not> quiet (get_trans res') (get_beh' res')\<close> \<open>time , get_state res' , get_beh' res' , get_beh res', def \<turnstile> <nand4 , get_trans res'> \<longrightarrow>\<^sub>c \<tau>_res\<close> \<open>time < Suc i\<close> bigstep2 case_bau nat_less_le)
      have "\<tau>_res = 0 \<or> \<tau>_res \<noteq> 0"
        by auto
      moreover
      { assume "\<tau>_res = 0"
        hence "next_event time \<tau>_res (get_state res') = {}"
        proof -
          have "next_state time \<tau>_res (get_state res') = get_state res'"
            using `\<tau>_res = 0` unfolding next_state_def Let_def  by (simp add: zero_fun_def zero_option_def)
          thus ?thesis
            unfolding next_event_alt_def  by auto
        qed
        hence "quiet (\<tau>_res (next_time time \<tau>_res := 0)) (next_event time \<tau>_res (get_state res'))"
          using `\<tau>_res = 0`  by (simp add: fun_upd_idem_iff quiet_def zero_fun_def)
        hence "res = (Suc i, next_state time \<tau>_res (get_state res'), next_event time \<tau>_res (get_state res'), Femto_VHDL_raw.add_to_beh2 (get_state res') (get_beh res') time def, 0)"
          using bau[OF bigstep3] `next_time time \<tau>_res < Suc i` by auto
        hence gb_res: "get_beh res = Femto_VHDL_raw.add_to_beh2 (get_state res') (get_beh res') time def"
          by auto
        have "time \<le> i"
          using \<open>time < Suc i\<close> less_Suc_eq_le by blast
        have "\<forall>n>time. get_beh res' n C = 0"
          by (metis b_simulate_fin_preserves_hist bigstep2_pre trans_removal zero_fun_def)
        hence "signal_of (def C) (get_beh res) C i = get_state res' C"
          using signal_of_add_to_beh2'[OF `time \<le> i` ] unfolding gb_res by auto
        have "signal_of (def A) \<tau> A i  = signal_of (def A) \<tau>' A i"
          using init'_modifies_local_strongest[OF `init' 0 def {} 0 def nand4 \<tau> \<tau>'` `A \<notin> set (signals_from nand4)`]
          using \<open>trans_post_raw C x (def C) \<tau> 0 0 = \<tau>'\<close> signal_of_trans_post by fastforce
        also have "... = signal_of (\<sigma>' A) \<tau>' A i"
          by (metis \<open>inf_time (to_trans_raw_sig \<tau>) A i = Some time1\<close> \<open>trans_post_raw C x (def C) \<tau> 0 0 = \<tau>'\<close> comp_apply option.simps(5) sig.distinct(3) signal_of_trans_post to_signal_def)
        also have "... = signal_of (\<sigma>' A) (\<tau>'(t':=0)) A i"
          by (smt \<open>next_state 0 \<tau>' def = \<sigma>'\<close> \<open>next_time 0 \<tau>' = t'\<close> comp_apply next_state_def next_time_at_least2 override_on_apply_in signal_of_rem_curr_trans_at_t)
        also have "... = signal_of (get_state res' A) (get_trans res') A i"
          using bau_signal_of[OF bigstep2_pre `A \<notin> set (signals_from nand4)` `time \<le> i` trans_removal]
          by blast
        also have "... = get_state res' A"
          by (metis (no_types, hide_lams) \<open>A \<notin> set (signals_from nand4)\<close> \<open>\<tau>_res = 0\<close> \<open>time , get_state res' , get_beh' res' , get_beh res', def \<turnstile> <nand4 , get_trans res'> \<longrightarrow>\<^sub>c \<tau>_res\<close> b_conc_exec_modifies_local_strongest signal_of_def zero_fun_def)
        finally have "signal_of (def A) \<tau> A i = get_state res' A"
          by auto
        have "signal_of (def B) \<tau> B i  = signal_of (def B) \<tau>' B i"
          using init'_modifies_local_strongest[OF `init' 0 def {} 0 def nand4 \<tau> \<tau>'` `B \<notin> set (signals_from nand4)`]
          using \<open>trans_post_raw C x (def C) \<tau> 0 0 = \<tau>'\<close> signal_of_trans_post by fastforce
        also have "... = signal_of (\<sigma>' B) \<tau>' B i"
          by (metis \<open>0 , def , {} , 0, def \<turnstile> <Bassign_trans C (Bnand (Bsig A) (Bsig B)) 0 , \<tau>> \<longrightarrow>\<^sub>s \<tau>'\<close>
          \<open>\<And>thesis. (\<And>time1 time2 time. \<lbrakk>inf_time (to_trans_raw_sig \<tau>) A i = Some time1; inf_time
          (to_trans_raw_sig \<tau>) B i = Some time2; time = max time1 time2\<rbrakk> \<Longrightarrow> thesis) \<Longrightarrow> thesis\<close> comp_def
          inf_time_trans_post option.simps(5) seq_cases_trans sig.distinct(5) to_signal_def)
        also have "... = signal_of (\<sigma>' B) (\<tau>'(t':=0)) B i"
          by (smt \<open>next_state 0 \<tau>' def = \<sigma>'\<close> \<open>next_time 0 \<tau>' = t'\<close> comp_apply next_state_def next_time_at_least2 override_on_apply_in signal_of_rem_curr_trans_at_t)
        also have "... = signal_of (get_state res' B) (get_trans res') B i"
          using bau_signal_of[OF bigstep2_pre `B \<notin> set (signals_from nand4)` `time \<le> i` trans_removal]
          by blast
        also have "... = get_state res' B"
          by (metis (no_types, hide_lams) \<open>B \<notin> set (signals_from nand4)\<close> \<open>\<tau>_res = 0\<close> \<open>time , get_state res' , get_beh' res' , get_beh res', def \<turnstile> <nand4 , get_trans res'> \<longrightarrow>\<^sub>c \<tau>_res\<close> b_conc_exec_modifies_local_strongest signal_of_def zero_fun_def)
        finally have "signal_of (def B) \<tau> B i = get_state res' B"
          by auto
        have "time , get_state res' , get_event res' , get_beh res', def  \<turnstile> <Bassign_trans C (Bnand (Bsig A) (Bsig B)) 0 , get_trans res'> \<longrightarrow>\<^sub>s \<tau>_res"
          using conc_cases(1)[OF `time, get_state res', get_event res', get_beh res', def \<turnstile> <nand4, get_trans res'> \<longrightarrow>\<^sub>c \<tau>_res`[unfolded nand4_def]]
          `\<not> disjnt {A, B} (get_event res')` by auto
        obtain x' where " time , get_state res' , get_beh' res' , get_beh res', def  \<turnstile> Bnand (Bsig A) (Bsig B) \<longrightarrow>\<^sub>b x'" and 
          \<tau>_res_def: " trans_post_raw C x' (get_state res' C) (get_trans res') time 0 = \<tau>_res"
          using seq_cases_trans[OF `time , get_state res' , get_event res' , get_beh res', def  \<turnstile> <Bassign_trans C (Bnand (Bsig A) (Bsig B)) 0 , get_trans res'> \<longrightarrow>\<^sub>s \<tau>_res`]
          by blast
        have "time , get_state res' , get_beh' res' , get_beh res', def  \<turnstile> Bsig A \<longrightarrow>\<^sub>b Bv (bval_of (get_state res' A))"
          by (smt \<open>0 , def , {} , 0, def \<turnstile> Bnand (Bsig A) (Bsig B) \<longrightarrow>\<^sub>b x\<close> \<open>signal_of (def A) \<tau> A i =
          get_state res' A\<close> \<open>x = Bv (\<not> (bval_of (def A) \<and> bval_of (def B)))\<close> assms(4) assms(6)
          beval_cases(1) beval_cases(9) beval_raw.intros(1) signal_of_preserve_well_typedness
          styping_def ty.simps(3) type_of.simps(1) type_of.simps(2) val.exhaust_sel)
        moreover have "time , get_state res' , get_beh' res' , get_beh res', def  \<turnstile> Bsig B \<longrightarrow>\<^sub>b Bv (bval_of (get_state res' B))"
          by (smt \<open>time , get_state res' , get_beh' res' , get_beh res', def \<turnstile> Bnand (Bsig A) (Bsig B)
          \<longrightarrow>\<^sub>b x'\<close> \<open>time , get_state res' , get_beh' res' , get_beh res', def \<turnstile> Bsig A \<longrightarrow>\<^sub>b Bv (bval_of
          (get_state res' A))\<close> beval_cases(9) beval_raw.intros(1) beval_raw_deterministic
          val.distinct(1) val.exhaust_sel)
        ultimately have "x' = Bv (\<not> (bval_of (get_state res' A) \<and> bval_of (get_state res' B)))"
          using beval_cases(9)[OF `time , get_state res' , get_beh' res' , get_beh res', def  \<turnstile> Bnand (Bsig A) (Bsig B) \<longrightarrow>\<^sub>b x'`]
          by (smt beval_cases(1) val.distinct(1))
        have "\<not> post_necessary_raw 0 (get_trans res') time C x' (get_state res' C)"
        proof (rule ccontr)
          assume "\<not> \<not> post_necessary_raw 0 (get_trans res') time C x' (get_state res' C)"
          hence "post_necessary_raw 0 (get_trans res') time C x' (get_state res' C)"
            by auto
          hence "\<tau>_res time C = post_raw C x' (get_trans res') (time + 0) time C"
            unfolding \<tau>_res_def[THEN sym] trans_post_raw_def by auto
          hence "next_time time \<tau>_res = time"
            by (simp add: \<open>\<tau>_res = 0\<close> post_raw_def zero_fun_def zero_option_def)
          thus "False"
            using `next_time time \<tau>_res < Suc i`  using \<open>time < Suc i\<close> 
            by (simp add: \<open>\<tau>_res = 0\<close>)
        qed
        moreover have "\<not> (\<exists>i\<le>time + 0 - 1. get_trans res' i C = Some x')"
          using b_simulate_fin_preserve_trans_removal[OF bigstep2_pre trans_removal] 
          by (metis (no_types, hide_lams) Suc_diff_1 \<open>t' < time \<or> t' = time\<close> add.right_neutral
          b_simulate_fin.intros(4) b_simulate_fin_deterministic bigstep2_pre comp_eq_dest_lhs
          diff_le_self fun_upd_same le_imp_less_Suc not_gr_zero not_le not_less_zero
          option.distinct(1) snd_conv zero_fun_def zero_option_def)
        ultimately have "x' = get_state res' C"
          unfolding post_necessary_raw_correctness by blast
        hence "bval_of (get_state res' C) \<longleftrightarrow> \<not> (bval_of (get_state res' A) \<and> bval_of (get_state res' B))"
          using `x' = Bv (\<not> (bval_of (get_state res' A) \<and> bval_of (get_state res' B)))`
          using val.sel(1) by presburger
        hence ?thesis
          using `signal_of (def A) \<tau> A i = get_state res' A` `signal_of (def B) \<tau> B i = get_state res' B`
          `signal_of (def C) (get_beh res) C i = get_state res' C` by auto }
      moreover
      { assume "\<tau>_res \<noteq> 0"
        have "time , get_state res' , get_event res' , get_beh res', def  \<turnstile> <Bassign_trans C (Bnand (Bsig A) (Bsig B)) 0 , get_trans res'> \<longrightarrow>\<^sub>s \<tau>_res"
          using conc_cases(1)[OF `time, get_state res', get_event res', get_beh res', def \<turnstile> <nand4, get_trans res'> \<longrightarrow>\<^sub>c \<tau>_res`[unfolded nand4_def]]
          `\<not> disjnt {A, B} (get_event res')` by auto
        obtain x' where " time , get_state res' , get_beh' res' , get_beh res', def  \<turnstile> Bnand (Bsig A) (Bsig B) \<longrightarrow>\<^sub>b x'" and 
          \<tau>_res_def: " trans_post_raw C x' (get_state res' C) (get_trans res') time 0 = \<tau>_res"
          using seq_cases_trans[OF `time , get_state res' , get_event res' , get_beh res', def  \<turnstile> <Bassign_trans C (Bnand (Bsig A) (Bsig B)) 0 , get_trans res'> \<longrightarrow>\<^sub>s \<tau>_res`]
          by blast
        have "\<And>n. n < time \<Longrightarrow> \<tau>_res n = 0"
          using b_conc_exec_preserve_trans_removal[OF `time, get_state res', get_event res', get_beh res', def \<turnstile> <nand4, get_trans res'> \<longrightarrow>\<^sub>c \<tau>_res`]
          b_simulate_fin_preserve_trans_removal[OF bigstep2_pre trans_removal] by auto
        have "next_time time \<tau>_res = time"
        proof (rule ccontr)
          assume "next_time time \<tau>_res \<noteq> time" 
          hence "time < next_time time \<tau>_res"
            by (metis \<open>\<And>n. n < time \<Longrightarrow> \<tau>_res n = 0\<close> nat_less_le next_time_at_least)
          hence "\<tau>_res (next_time time \<tau>_res) C = None"
            unfolding \<tau>_res_def[THEN sym] trans_post_raw_def preempt_raw_def post_raw_def
            by (smt add.right_neutral dual_order.strict_implies_order fun_upd_eqD fun_upd_triv nat_neq_iff)
          have "next_time time \<tau>_res = (LEAST n. dom (\<tau>_res n) \<noteq> {})"
            using `\<tau>_res \<noteq> 0` unfolding next_time_def by auto
          hence "\<tau>_res time = 0"
            using `time < next_time time \<tau>_res`  using next_time_at_least2 by blast
          have "\<exists>n. dom (\<tau>_res n) \<noteq> {}"
            using `\<tau>_res \<noteq> 0` unfolding dom_def zero_fun_def zero_option_def by fastforce
          have "\<tau>_res (next_time time \<tau>_res) \<noteq> 0"
            by (metis (mono_tags, lifting) LeastI \<open>\<exists>n. dom (\<tau>_res n) \<noteq> {}\<close> \<open>next_time time \<tau>_res = (LEAST n. dom (\<tau>_res n) \<noteq> {})\<close> dom_eq_empty_conv zero_map)
          hence "\<tau>_res (next_time time \<tau>_res) A \<noteq> None \<or> \<tau>_res (next_time time \<tau>_res) B \<noteq> None "
            using `\<tau>_res (next_time time \<tau>_res) C = None` unfolding zero_fun_def zero_option_def 
            by (metis sig.exhaust)
          hence "get_trans res' (next_time time \<tau>_res) A \<noteq> None \<or> get_trans res' (next_time time \<tau>_res) B \<noteq> None"
            using b_conc_exec_modifies_local_strongest[OF `time, get_state res', get_event res', get_beh res', def \<turnstile> <nand4, get_trans res'> \<longrightarrow>\<^sub>c \<tau>_res`]
            by (simp add: \<open>A \<notin> set (signals_from nand4)\<close> \<open>B \<notin> set (signals_from nand4)\<close>)
          hence "(\<tau>'(t' := 0)) (next_time time \<tau>_res) A \<noteq> None \<or> (\<tau>'(t' := 0)) (next_time time \<tau>_res) B \<noteq> None"
            using b_simulate_fin_get_trans_gt_maxtime[OF bigstep2_pre `A \<notin> set (signals_from nand4)`]
            using b_simulate_fin_get_trans_gt_maxtime[OF bigstep2_pre `B \<notin> set (signals_from nand4)`]
            by (simp add: \<open>time < next_time time \<tau>_res\<close>)
          hence "\<tau>' (next_time time \<tau>_res) A \<noteq> None \<or> \<tau>' (next_time time \<tau>_res) B \<noteq> None"
            by (metis \<open>\<And>n. n < time \<Longrightarrow> \<tau>_res n = 0\<close> \<open>\<tau>_res (next_time time \<tau>_res) \<noteq> 0\<close> \<open>next_time time \<tau>_res \<noteq> time\<close> \<open>t' < time \<or> t' = time\<close> fun_upd_other)
          hence "\<tau> (next_time time \<tau>_res) A \<noteq> None \<or> \<tau> (next_time time \<tau>_res) B \<noteq> None"
            by (metis \<open>\<And>thesis. (\<And>x. \<lbrakk>0 , def , {} , 0, def \<turnstile> Bnand (Bsig A) (Bsig B) \<longrightarrow>\<^sub>b x;
            trans_post_raw C x (def C) \<tau> 0 0 = \<tau>'\<rbrakk> \<Longrightarrow> thesis) \<Longrightarrow> thesis\<close> sig.distinct(3)
            sig.distinct(5) to_trans_raw_sig_def trans_post_raw_diff_sig)
          thus "False"
            using inf_time_someE[OF \<open>inf_time (to_trans_raw_sig \<tau>) A i = Some time1\<close>]
            using inf_time_someE[OF \<open>inf_time (to_trans_raw_sig \<tau>) B i = Some time2\<close>]
            \<open>time = max time1 time2\<close> \<open>time < next_time time \<tau>_res\<close> \<open>next_time time \<tau>_res < Suc i\<close>
            by (metis domIff max_less_iff_conj not_le not_less_eq_eq to_trans_raw_sig_def)
        qed
        hence "\<tau>_res time \<noteq> 0"
          using `\<tau>_res \<noteq> 0` unfolding zero_fun_def zero_option_def next_time_def 
          by (metis (mono_tags, lifting) LeastI_ex dom_eq_empty_conv)
        have " get_trans res' time = 0"
          using get_trans_res_maxtime[OF bigstep2_pre ] by auto          
        hence "\<tau>_res time A = 0" and "\<tau>_res time B = 0"
          using b_conc_exec_modifies_local_strongest[OF `time, get_state res', get_event res', get_beh res', def \<turnstile> <nand4, get_trans res'> \<longrightarrow>\<^sub>c \<tau>_res` `A \<notin> set (signals_from nand4)`]
          using b_conc_exec_modifies_local_strongest[OF `time, get_state res', get_event res', get_beh res', def \<turnstile> <nand4, get_trans res'> \<longrightarrow>\<^sub>c \<tau>_res` `B \<notin> set (signals_from nand4)`]
          by (metis zero_fun_def)+
        hence " A \<notin> next_event time \<tau>_res (get_state res')" and " B \<notin> next_event time \<tau>_res (get_state res')"
          unfolding next_event_alt_def next_state_def \<open>next_time time \<tau>_res = time\<close> 
          by (smt domIff mem_Collect_eq override_on_def zero_option_def)+
        hence "disjnt {A, B} (next_event time \<tau>_res (get_state res'))"
          by auto
        have "\<tau>_res time C \<noteq> 0"
        proof (rule ccontr)
          assume "\<not> \<tau>_res time C \<noteq> 0" hence "\<tau>_res time C = 0" by auto
          hence "\<tau>_res time = 0"
            using `\<tau>_res time A = 0` `\<tau>_res time B = 0` 
            unfolding zero_fun_def zero_option_def  by (metis sig.exhaust)
          with `\<tau>_res time \<noteq> 0` show False 
            by auto
        qed
        have "post_necessary_raw 0 (get_trans res') time C x' (get_state res' C)"
        proof (rule ccontr)
          assume "\<not> post_necessary_raw 0 (get_trans res') time C x' (get_state res' C)"
          hence "\<tau>_res time C = 0"
            unfolding \<tau>_res_def[THEN sym] trans_post_raw_def preempt_raw_def by (auto simp add: zero_option_def)
          with `\<tau>_res time C \<noteq> 0` show False
            by auto
        qed
        hence "\<tau>_res time C = Some x'"
          unfolding \<tau>_res_def[THEN sym] trans_post_raw_def post_raw_def by auto
        have "\<not> (\<exists>i\<le>time + 0 - 1. get_trans res' i C = Some x')"
          using b_simulate_fin_preserve_trans_removal[OF bigstep2_pre trans_removal] 
          by (metis (no_types, hide_lams) Suc_diff_1 \<open>t' < time \<or> t' = time\<close> add.right_neutral
          b_simulate_fin.intros(4) b_simulate_fin_deterministic bigstep2_pre comp_eq_dest_lhs
          diff_le_self fun_upd_same le_imp_less_Suc not_gr_zero not_le not_less_zero
          option.distinct(1) snd_conv zero_fun_def zero_option_def)
        hence "get_state res' C \<noteq> x'"
          using `post_necessary_raw 0 (get_trans res') time C x' (get_state res' C)`
          unfolding post_necessary_raw_correctness2 
          by (metis (no_types, lifting) Suc_diff_1 \<open>next_time time \<tau>_res = time\<close> \<open>post_necessary_raw
          0 (get_trans res') time C x' (get_state res' C)\<close> \<tau>_res_def add.right_neutral
          le_imp_less_Suc next_time_at_least2 option.distinct(1) order.asym post_raw_def
          trans_post_raw_def zero_fun_def zero_option_def)
        hence "get_state res'  C \<noteq> the (\<tau>_res time C)"
          by (simp add: \<open>\<tau>_res time C = Some x'\<close>)
        hence "C \<in> (next_event time \<tau>_res (get_state res'))" 
          unfolding next_event_alt_def next_state_def 
          by (smt \<open>\<tau>_res time C \<noteq> 0\<close> \<open>next_time time \<tau>_res = time\<close> comp_def domIff mem_Collect_eq override_on_apply_in zero_option_def)
        hence "next_time time
            \<tau>_res , next_state time \<tau>_res
                     (get_state res') , next_event time \<tau>_res (get_state res') , Femto_VHDL_raw.add_to_beh2 (get_state res') (get_beh res') time def, def  \<turnstile> <nand4 , \<tau>_res
           (next_time time \<tau>_res := 0)> \<longrightarrow>\<^sub>c  \<tau>_res (next_time time \<tau>_res := 0)"
          using `disjnt {A, B} (next_event time \<tau>_res (get_state res'))` 
          unfolding nand4_def by (intro b_conc_exec.intros(1))
        have " \<not> quiet (\<tau>_res(next_time time \<tau>_res := 0)) (next_event time \<tau>_res (get_state res'))"
          by (metis \<open>C \<in> next_event time \<tau>_res (get_state res')\<close> empty_iff quiet_def)

        have "(\<tau>_res (next_time time \<tau>_res := 0)) \<noteq> 0 \<Longrightarrow> Suc i \<le> next_time (next_time time \<tau>_res) (\<tau>_res (next_time time \<tau>_res := 0))"
          unfolding `next_time time \<tau>_res = time`
        proof (rule ccontr)
          assume " \<tau>_res(time := 0) \<noteq> 0"
          assume "\<not> Suc i \<le> next_time time (\<tau>_res (time := 0))"
          hence "next_time time (\<tau>_res (time := 0)) < Suc i"
            by auto
          have "to_trans_raw_sig (\<tau>_res (time := 0)) C = 0"
            using `\<And>n. n < time \<Longrightarrow> \<tau>_res n = 0`
            using `post_necessary_raw 0 (get_trans res') time C x' (get_state res' C)`
            unfolding to_trans_raw_sig_def \<tau>_res_def[THEN sym] trans_post_raw_def post_raw_def
            zero_fun_def zero_option_def 
            by (intro ext) auto
          have tr: "\<And>n. n < time \<Longrightarrow> (\<tau>_res (time := 0)) n = 0"
            using `\<And>n. n < time \<Longrightarrow> \<tau>_res n = 0` by auto
          have "time \<le> next_time time (\<tau>_res (time := 0))"
            by (intro next_time_at_least[OF tr] )
          moreover have "time \<noteq> next_time time (\<tau>_res (time := 0))"
            by (smt Suc_eq_plus1 Suc_n_not_le_n fun_upd_same less_Suc_eq next_time_at_least next_time_def tr)
          ultimately have "time < next_time time (\<tau>_res (time := 0))"
            by auto
          have "(\<tau>_res(time := 0)) (next_time time (\<tau>_res (time := 0))) \<noteq> 0"
            using `\<tau>_res (time := 0) \<noteq> 0` unfolding next_time_def zero_fun_def zero_option_def
          proof -
            assume a1: "\<tau>_res(time := Map.empty) \<noteq> (\<lambda>x. Map.empty)"
            have f2: "\<And>n. {s. (\<tau>_res(time := Map.empty)) n s \<noteq> None} = {} \<or> dom ((\<tau>_res(time := Map.empty)) (LEAST n. dom ((\<tau>_res(time := Map.empty)) n) \<noteq> {})) \<noteq> {}"
              by (metis (mono_tags, lifting) LeastI_ex a1 dom_eq_empty_conv) 
            obtain nn :: nat and ss :: sig where f3: "(\<tau>_res(time := Map.empty)) nn ss \<noteq> None"
              using a1 by meson
            obtain ssa :: "(sig \<Rightarrow> val option) \<Rightarrow> sig" where f4: "\<And>f s fa. (dom f \<noteq> {} \<or> f (s::sig) = (None::val option)) \<and> (fa (ssa fa) \<noteq> None \<or> dom fa = {})"
              by (metis (no_types) dom_eq_empty_conv)
            then have "{s. (\<tau>_res(time := Map.empty)) (LEAST n. dom ((\<tau>_res(time := Map.empty)) n) \<noteq> {}) s \<noteq> None} \<noteq> {}"
              using f3 f2 by (metis (no_types) dom_def)
            then have "{s. (\<tau>_res(time := Map.empty)) (if \<forall>n s. (\<tau>_res(time := Map.empty)) n s = None then Suc time else LEAST n. dom ((\<tau>_res(time := Map.empty)) n) \<noteq> {}) s \<noteq> None} = {} \<longrightarrow> (\<forall>n s. (\<tau>_res(time := Map.empty)) n s = None)"
              by presburger
            then have "\<exists>s. (\<tau>_res(time := Map.empty)) (if \<forall>n s. (\<tau>_res(time := Map.empty)) n s = None then Suc time else LEAST n. dom ((\<tau>_res(time := Map.empty)) n) \<noteq> {}) s \<noteq> None"
              using f4 f3 by blast
            then show "(\<tau>_res(time := Map.empty)) (if \<tau>_res(time := Map.empty) = (\<lambda>n. Map.empty) then time + 1 else LEAST n. dom ((\<tau>_res(time := Map.empty)) n) \<noteq> {}) \<noteq> Map.empty"
              by (metis Suc_eq_plus1)
          qed
          hence "(\<tau>_res(time := 0)) (next_time time (\<tau>_res (time := 0))) A \<noteq> 0 \<or> 
                (\<tau>_res(time := 0)) (next_time time (\<tau>_res (time := 0))) B \<noteq> 0" 
            using `to_trans_raw_sig (\<tau>_res (time := 0)) C = 0` unfolding to_trans_raw_sig_def
          proof -
            assume a1: "(\<lambda>n. (\<tau>_res(time := 0)) n C) = 0"
            obtain ss :: "sig set \<Rightarrow> sig set \<Rightarrow> sig" where
              "\<forall>x0 x1. (\<exists>v2. v2 \<in> x1 \<and> v2 \<notin> x0) = (ss x0 x1 \<in> x1 \<and> ss x0 x1 \<notin> x0)"
              by moura
            then have f2: "\<forall>S Sa. ss Sa S \<in> S \<and> ss Sa S \<notin> Sa \<or> S \<subseteq> Sa"
              by (meson subsetI)
            then have "dom (0::sig \<Rightarrow> val option) \<subseteq> {}"
              by (meson domIff zero_map)
            then have f3: "\<not> dom ((\<tau>_res(time := 0)) (next_time time (\<tau>_res(time := 0)))) \<subseteq> {}"
              using \<open>(\<tau>_res(time := 0)) (next_time time (\<tau>_res(time := 0))) \<noteq> 0\<close> by auto
            have "(\<tau>_res(time := 0)) (next_time time (\<tau>_res(time := 0))) C = None"
              using a1 by (metis (no_types) zero_map)
            then show ?thesis
              using f3 f2 by (metis (full_types) domIff sig.exhaust zero_option_def)
          qed
          hence "get_trans res' (next_time time (\<tau>_res (time := 0))) A \<noteq> 0 \<or> 
                 get_trans res' (next_time time (\<tau>_res (time := 0))) B \<noteq> 0"
            using b_conc_exec_modifies_local_strongest[OF `time, get_state res', get_event res', get_beh res', def \<turnstile> <nand4, get_trans res'> \<longrightarrow>\<^sub>c \<tau>_res` `A \<notin> set (signals_from nand4)`]
            using b_conc_exec_modifies_local_strongest[OF `time, get_state res', get_event res', get_beh res', def \<turnstile> <nand4, get_trans res'> \<longrightarrow>\<^sub>c \<tau>_res` `A \<notin> set (signals_from nand4)`]
            using `time < next_time time (\<tau>_res (time := 0))` 
            using \<open>B \<notin> set (signals_from nand4)\<close> \<open>time , get_state res' , get_beh' res' , get_beh res', def \<turnstile> <nand4 , get_trans res'> \<longrightarrow>\<^sub>c \<tau>_res\<close> b_conc_exec_modifies_local_strongest by fastforce
          hence "(\<tau>'(t' := 0)) (next_time time (\<tau>_res(time := 0))) A \<noteq> None \<or> (\<tau>'(t' := 0)) (next_time time (\<tau>_res(time := 0))) B \<noteq> None"
            using b_simulate_fin_get_trans_gt_maxtime[OF bigstep2_pre `A \<notin> set (signals_from nand4)`]
            using b_simulate_fin_get_trans_gt_maxtime[OF bigstep2_pre `B \<notin> set (signals_from nand4)`]
            by (simp add: \<open>time < next_time time (\<tau>_res(time := 0))\<close> zero_option_def)
          hence "\<tau>' (next_time time (\<tau>_res(time := 0))) A \<noteq> None \<or> \<tau>' (next_time time (\<tau>_res(time := 0))) B \<noteq> None"
            by (metis fun_upd_other fun_upd_same zero_map)
          hence "\<tau> (next_time time (\<tau>_res(time := 0))) A \<noteq> None \<or> \<tau> (next_time time (\<tau>_res(time := 0))) B \<noteq> None"
            by (metis \<open>\<And>thesis. (\<And>x. \<lbrakk>0 , def , {} , 0, def \<turnstile> Bnand (Bsig A) (Bsig B) \<longrightarrow>\<^sub>b x;
            trans_post_raw C x (def C) \<tau> 0 0 = \<tau>'\<rbrakk> \<Longrightarrow> thesis) \<Longrightarrow> thesis\<close> sig.distinct(3)
            sig.distinct(5) to_trans_raw_sig_def trans_post_raw_diff_sig)
          thus "False"
            using inf_time_someE[OF \<open>inf_time (to_trans_raw_sig \<tau>) A i = Some time1\<close>]
            using inf_time_someE[OF \<open>inf_time (to_trans_raw_sig \<tau>) B i = Some time2\<close>]
            \<open>time = max time1 time2\<close> \<open>time < next_time time (\<tau>_res(time:= 0))\<close> \<open>next_time time (\<tau>_res(time := 0)) < Suc i\<close>
            by (metis domIff max_less_iff_conj not_le not_less_eq_eq to_trans_raw_sig_def)          
        qed
        have "(\<tau>_res (next_time time \<tau>_res := 0)) = 0 \<Longrightarrow> next_time (next_time time \<tau>_res) (\<tau>_res (next_time time \<tau>_res := 0)) \<le> Suc i"
          unfolding `next_time time \<tau>_res = time` using `time < Suc i` by auto
        have "(\<tau>_res (next_time time \<tau>_res := 0)) = 0 \<or> (\<tau>_res (next_time time \<tau>_res := 0)) \<noteq> 0"
          by auto
        moreover
        { assume "(\<tau>_res (next_time time \<tau>_res := 0)) = 0"
          hence " next_time (next_time time \<tau>_res) (\<tau>_res (next_time time \<tau>_res := 0)) \<le> Suc i"
            using \<open>\<tau>_res(next_time time \<tau>_res := 0) = 0 \<Longrightarrow> next_time (next_time time \<tau>_res) (\<tau>_res(next_time time \<tau>_res := 0)) \<le> Suc i\<close> by blast
          hence bigstep4: " Suc i, next_time (next_time time \<tau>_res) (\<tau>_res (next_time time \<tau>_res := 0)) , 
                                   next_state (next_time time \<tau>_res) (\<tau>_res (next_time time \<tau>_res := 0)) (next_state time \<tau>_res (get_state res')) , 
                                   next_event (next_time time \<tau>_res) (\<tau>_res (next_time time \<tau>_res := 0)) (next_state time \<tau>_res (get_state res')) , 
                                   Femto_VHDL_raw.add_to_beh2 (next_state time \<tau>_res (get_state res')) (Femto_VHDL_raw.add_to_beh2 (get_state res') (get_beh res') time def) (next_time time \<tau>_res) def, def \<turnstile> 
                                    <nand4 , (\<tau>_res (next_time time \<tau>_res := 0)) (next_time (next_time time \<tau>_res) (\<tau>_res (next_time time \<tau>_res := 0)) := 0)> \<leadsto> res"
            using bau[OF bigstep3] `next_time time \<tau>_res < Suc i` 
            by (smt \<open>C \<in> next_event time \<tau>_res (get_state res')\<close> \<open>next_time time \<tau>_res , next_state time \<tau>_res (get_state res') , next_event time \<tau>_res (get_state res') , Femto_VHDL_raw.add_to_beh2 (get_state res') (get_beh res') time def, def \<turnstile> <nand4 , \<tau>_res (next_time time \<tau>_res := 0)> \<longrightarrow>\<^sub>c \<tau>_res (next_time time \<tau>_res := 0)\<close> bigstep3 case_bau empty_iff quiet_def)
          have "next_event (next_time time \<tau>_res) (\<tau>_res (next_time time \<tau>_res := 0)) (next_state time \<tau>_res (get_state res')) = {}"
            unfolding `(\<tau>_res (next_time time \<tau>_res := 0)) = 0` next_event_alt_def  next_state_def
            Let_def zero_fun_def zero_option_def 
            by (smt \<open>\<tau>_res(next_time time \<tau>_res := 0) = 0\<close> domIff empty_Collect_eq fun_upd_apply override_on_apply_notin zero_fun_def zero_map)
          have " (\<tau>_res (next_time time \<tau>_res := 0)) (next_time (next_time time \<tau>_res) (\<tau>_res (next_time time \<tau>_res := 0)) := 0) = 0"
            using `(\<tau>_res (next_time time \<tau>_res := 0)) = 0`  by (simp add: fun_upd_idem_iff zero_fun_def)
          have "next_time (next_time time \<tau>_res) (\<tau>_res (next_time time \<tau>_res := 0)) < Suc i \<or> next_time (next_time time \<tau>_res) (\<tau>_res (next_time time \<tau>_res := 0)) = Suc i"
            using \<open>next_time (next_time time \<tau>_res) (\<tau>_res(next_time time \<tau>_res := 0)) \<le> Suc i\<close> le_imp_less_or_eq by blast
          moreover
          { assume "next_time (next_time time \<tau>_res) (\<tau>_res (next_time time \<tau>_res := 0)) = Suc i"
            hence "res =
     (Suc i, next_state (next_time time \<tau>_res) (\<tau>_res(next_time time \<tau>_res := 0)) (next_state time \<tau>_res (get_state res')),
      next_event (next_time time \<tau>_res) (\<tau>_res(next_time time \<tau>_res := 0)) (next_state time \<tau>_res (get_state res')),
      Femto_VHDL_raw.add_to_beh2 (next_state time \<tau>_res (get_state res'))
       (Femto_VHDL_raw.add_to_beh2 (get_state res') (get_beh res') time def) (next_time time \<tau>_res) def,
      \<tau>_res(next_time time \<tau>_res := 0, next_time (next_time time \<tau>_res) (\<tau>_res(next_time time \<tau>_res := 0)) := 0))"
              using bau[OF bigstep4] by auto
            hence gb_res: "get_beh res = Femto_VHDL_raw.add_to_beh2 (next_state time \<tau>_res (get_state res')) (Femto_VHDL_raw.add_to_beh2 (get_state res') (get_beh res') time def) (next_time time \<tau>_res) def"
              by auto } 
          moreover
          { assume "next_time (next_time time \<tau>_res) (\<tau>_res (next_time time \<tau>_res := 0)) < Suc i"
            hence "res =
     (Suc i, next_state (next_time time \<tau>_res) (\<tau>_res(next_time time \<tau>_res := 0)) (next_state time \<tau>_res (get_state res')),
      next_event (next_time time \<tau>_res) (\<tau>_res(next_time time \<tau>_res := 0)) (next_state time \<tau>_res (get_state res')),
      Femto_VHDL_raw.add_to_beh2 (next_state time \<tau>_res (get_state res'))
       (Femto_VHDL_raw.add_to_beh2 (get_state res') (get_beh res') time def) (next_time time \<tau>_res) def,
      0)"
              using bau[OF bigstep4] 
              by (smt \<open>\<tau>_res (next_time time \<tau>_res := 0, next_time (next_time time \<tau>_res)
              (\<tau>_res(next_time time \<tau>_res := 0)) := 0) = 0\<close> \<open>next_event (next_time time \<tau>_res)
              (\<tau>_res(next_time time \<tau>_res := 0)) (next_state time \<tau>_res (get_state res')) = {}\<close>
              quiet_def)
            hence "get_beh res = Femto_VHDL_raw.add_to_beh2 (next_state time \<tau>_res (get_state res'))
       (Femto_VHDL_raw.add_to_beh2 (get_state res') (get_beh res') time def) (next_time time \<tau>_res) def"
              by auto }
          ultimately have gb_res: "get_beh res = Femto_VHDL_raw.add_to_beh2 (next_state time \<tau>_res (get_state res')) (Femto_VHDL_raw.add_to_beh2 (get_state res') (get_beh res') time def) (next_time time \<tau>_res) def"
            by auto
          have " (next_time time \<tau>_res) \<le> i"
            using \<open>next_time time \<tau>_res < Suc i\<close> less_Suc_eq_le by blast
          have "signal_of (def C) (get_beh res) C i = (next_state time \<tau>_res (get_state res')) C"
            unfolding gb_res
            apply (intro signal_of_add_to_beh2'[OF `next_time time \<tau>_res \<le> i`] )
            by (smt Femto_VHDL_raw.add_to_beh2_def \<open>next_time time \<tau>_res = time\<close> b_simulate_fin_preserves_hist bigstep2_pre fun_upd_other nat_neq_iff trans_removal zero_fun_def)
          also have "... = the (\<tau>_res time C)"
            unfolding next_state_def `next_time time \<tau>_res = time` Let_def 
            by (metis \<open>\<tau>_res time C \<noteq> 0\<close> comp_apply domIff override_on_apply_in zero_option_def)
          also have "... = x'"
            by (simp add: \<open>\<tau>_res time C = Some x'\<close>)
          finally have "signal_of (def C) (get_beh res) C i = x'"
            by auto
          have "signal_of (def A) \<tau> A i  = signal_of (def A) \<tau>' A i"
            using init'_modifies_local_strongest[OF `init' 0 def {} 0 def nand4 \<tau> \<tau>'` `A \<notin> set (signals_from nand4)`]
            using \<open>trans_post_raw C x (def C) \<tau> 0 0 = \<tau>'\<close> signal_of_trans_post by fastforce
          also have "... = signal_of (\<sigma>' A) \<tau>' A i"
            by (metis \<open>inf_time (to_trans_raw_sig \<tau>) A i = Some time1\<close> \<open>trans_post_raw C x (def C) \<tau> 0 0 = \<tau>'\<close> comp_apply option.simps(5) sig.distinct(3) signal_of_trans_post to_signal_def)
          also have "... = signal_of (\<sigma>' A) (\<tau>'(t':=0)) A i"
            by (smt \<open>next_state 0 \<tau>' def = \<sigma>'\<close> \<open>next_time 0 \<tau>' = t'\<close> comp_apply next_state_def next_time_at_least2 override_on_apply_in signal_of_rem_curr_trans_at_t)
          also have "... = signal_of (get_state res' A) (get_trans res') A i"
            using bau_signal_of[OF bigstep2_pre `A \<notin> set (signals_from nand4)` _ trans_removal] `time < Suc i`
            using less_Suc_eq_le by blast
          also have "... = get_state res' A"
            by (metis (mono_tags, lifting) \<open>A \<notin> set (signals_from nand4)\<close> \<open>\<tau>_res time A = 0\<close>
            \<open>\<tau>_res(next_time time \<tau>_res := 0) = 0\<close> \<open>next_time time \<tau>_res = time\<close> \<open>time , get_state
            res' , get_beh' res' , get_beh res', def \<turnstile> <nand4 , get_trans res'> \<longrightarrow>\<^sub>c \<tau>_res\<close>
            b_conc_exec_modifies_local_strongest fun_upd_def signal_of_def zero_fun_def)
          finally have "signal_of (def A) \<tau> A i = get_state res' A"
            by auto
          have "signal_of (def B) \<tau> B i  = signal_of (def B) \<tau>' B i"
            using init'_modifies_local_strongest[OF `init' 0 def {} 0 def nand4 \<tau> \<tau>'` `B \<notin> set (signals_from nand4)`]
            using \<open>trans_post_raw C x (def C) \<tau> 0 0 = \<tau>'\<close> signal_of_trans_post by fastforce
          also have "... = signal_of (\<sigma>' B) \<tau>' B i"
            by (metis \<open>inf_time (to_trans_raw_sig \<tau>) B i = Some time2\<close> \<open>trans_post_raw C x (def C) \<tau> 0 0 = \<tau>'\<close> comp_apply inf_time_trans_post option.simps(5) sig.distinct(5) to_signal_def)
          also have "... = signal_of (\<sigma>' B) (\<tau>'(t':=0)) B i"
            by (smt \<open>next_state 0 \<tau>' def = \<sigma>'\<close> \<open>next_time 0 \<tau>' = t'\<close> comp_apply next_state_def next_time_at_least2 override_on_apply_in signal_of_rem_curr_trans_at_t)
          also have "... = signal_of (get_state res' B) (get_trans res') B i"
            using bau_signal_of[OF bigstep2_pre `B \<notin> set (signals_from nand4)` _ trans_removal] `time < Suc i`
            using less_Suc_eq_le by blast
          also have "... = get_state res' B"
            by (metis (mono_tags, lifting) \<open>B \<notin> set (signals_from nand4)\<close> \<open>\<tau>_res time B = 0\<close>
            \<open>\<tau>_res(next_time time \<tau>_res := 0) = 0\<close> \<open>next_time time \<tau>_res = time\<close> \<open>time , get_state
            res' , get_beh' res' , get_beh res', def \<turnstile> <nand4 , get_trans res'> \<longrightarrow>\<^sub>c \<tau>_res\<close>
            b_conc_exec_modifies_local_strongest fun_upd_def signal_of_def zero_fun_def)
          finally have "signal_of (def B) \<tau> B i = get_state res' B"
            by auto
          have "time , get_state res' , get_beh' res' , get_beh res', def  \<turnstile> Bsig A \<longrightarrow>\<^sub>b Bv (bval_of (get_state res' A))"
            by (smt \<open>0 , def , {} , 0, def \<turnstile> Bnand (Bsig A) (Bsig B) \<longrightarrow>\<^sub>b x\<close> \<open>signal_of (def A) \<tau> A i =
            get_state res' A\<close> \<open>x = Bv (\<not> (bval_of (def A) \<and> bval_of (def B)))\<close> assms(4) assms(6)
            beval_cases(1) beval_cases(9) beval_raw.intros(1) signal_of_preserve_well_typedness
            styping_def ty.simps(3) type_of.simps(1) type_of.simps(2) val.exhaust_sel)
          moreover have "time , get_state res' , get_beh' res' , get_beh res', def  \<turnstile> Bsig B \<longrightarrow>\<^sub>b Bv (bval_of (get_state res' B))"
            by (smt \<open>time , get_state res' , get_beh' res' , get_beh res', def \<turnstile> Bnand (Bsig A) (Bsig B)
            \<longrightarrow>\<^sub>b x'\<close> \<open>time , get_state res' , get_beh' res' , get_beh res', def \<turnstile> Bsig A \<longrightarrow>\<^sub>b Bv (bval_of
            (get_state res' A))\<close> beval_cases(9) beval_raw.intros(1) beval_raw_deterministic
            val.distinct(1) val.exhaust_sel)
          ultimately have "x' = Bv (\<not> (bval_of (get_state res' A) \<and> bval_of (get_state res' B)))"
            using beval_cases(9)[OF `time , get_state res' , get_beh' res' , get_beh res', def  \<turnstile> Bnand (Bsig A) (Bsig B) \<longrightarrow>\<^sub>b x'`]
            by (smt beval_cases(1) val.distinct(1))
          hence ?thesis
            using \<open>signal_of (def A) \<tau> A i = get_state res' A\<close> \<open>signal_of (def B) \<tau> B i = get_state res' B\<close> \<open>signal_of (def C) (get_beh res) C i = x'\<close> 
            by auto }
        moreover
        { assume " (\<tau>_res (next_time time \<tau>_res := 0)) \<noteq> 0"
          hence "Suc i \<le> next_time (next_time time \<tau>_res) (\<tau>_res (next_time time \<tau>_res := 0))"
            using \<open>\<tau>_res(next_time time \<tau>_res := 0) \<noteq> 0 \<Longrightarrow> Suc i \<le> next_time (next_time time \<tau>_res)
            (\<tau>_res(next_time time \<tau>_res := 0))\<close> by blast
          hence "Suc i < next_time (next_time time \<tau>_res) (\<tau>_res (next_time time \<tau>_res := 0)) \<or> Suc i = next_time (next_time time \<tau>_res) (\<tau>_res (next_time time \<tau>_res := 0))"        
            by auto
          moreover
          { assume "Suc i = next_time (next_time time \<tau>_res) (\<tau>_res (next_time time \<tau>_res := 0))"
            hence bigstep4: " Suc i, next_time (next_time time \<tau>_res) (\<tau>_res (next_time time \<tau>_res := 0)) , 
                                     next_state (next_time time \<tau>_res) (\<tau>_res (next_time time \<tau>_res := 0)) (next_state time \<tau>_res (get_state res')) , 
                                     next_event (next_time time \<tau>_res) (\<tau>_res (next_time time \<tau>_res := 0)) (next_state time \<tau>_res (get_state res')) , 
                                     Femto_VHDL_raw.add_to_beh2 (next_state time \<tau>_res (get_state res')) (Femto_VHDL_raw.add_to_beh2 (get_state res') (get_beh res') time def) (next_time time \<tau>_res) def, def \<turnstile> 
                                      <nand4 , (\<tau>_res (next_time time \<tau>_res := 0)) (next_time (next_time time \<tau>_res) (\<tau>_res (next_time time \<tau>_res := 0)) := 0)> \<leadsto> res"
              using bau[OF bigstep3] `next_time time \<tau>_res < Suc i` 
              by (smt \<open>Suc i \<le> next_time (next_time time \<tau>_res) (\<tau>_res(next_time time \<tau>_res := 0))\<close> \<open>\<tau>_res(next_time time \<tau>_res := 0) \<noteq> 0\<close> \<open>next_time time \<tau>_res , next_state time \<tau>_res (get_state res') , next_event time \<tau>_res (get_state res') , Femto_VHDL_raw.add_to_beh2 (get_state res') (get_beh res') time def, def \<turnstile> <nand4 , \<tau>_res (next_time time \<tau>_res := 0)> \<longrightarrow>\<^sub>c \<tau>_res (next_time time \<tau>_res := 0)\<close> bigstep3 case_bau quiet_def)
            hence "res =
     (Suc i, next_state (next_time time \<tau>_res) (\<tau>_res(next_time time \<tau>_res := 0)) (next_state time \<tau>_res (get_state res')),
      next_event (next_time time \<tau>_res) (\<tau>_res(next_time time \<tau>_res := 0)) (next_state time \<tau>_res (get_state res')),
      Femto_VHDL_raw.add_to_beh2 (next_state time \<tau>_res (get_state res'))
       (Femto_VHDL_raw.add_to_beh2 (get_state res') (get_beh res') time def) (next_time time \<tau>_res) def,
      \<tau>_res(next_time time \<tau>_res := 0, next_time (next_time time \<tau>_res) (\<tau>_res(next_time time \<tau>_res := 0)) := 0))"
              using bau[OF bigstep4] 
              using \<open>Suc i = next_time (next_time time \<tau>_res) (\<tau>_res(next_time time \<tau>_res := 0))\<close> by fastforce
            hence "get_beh res = Femto_VHDL_raw.add_to_beh2 (next_state time \<tau>_res (get_state res')) (Femto_VHDL_raw.add_to_beh2 (get_state res') (get_beh res') time def) (next_time time \<tau>_res) def"
              by auto }
          moreover
          { assume "Suc i < next_time (next_time time \<tau>_res) (\<tau>_res (next_time time \<tau>_res := 0))"
            hence "res =
           (Suc i, next_state time \<tau>_res (get_state res'), {},
            Femto_VHDL_raw.add_to_beh2 (next_state time \<tau>_res (get_state res'))
             (Femto_VHDL_raw.add_to_beh2 (get_state res') (get_beh res') time def) (next_time time \<tau>_res) def, \<tau>_res (next_time time \<tau>_res := 0))"
              using bau[OF bigstep3] `next_time time \<tau>_res < Suc i` \<open> \<not> quiet (\<tau>_res(next_time time \<tau>_res := 0)) (next_event time \<tau>_res (get_state res'))\<close>
              \<open>next_time time
            \<tau>_res , next_state time \<tau>_res
                     (get_state res') , next_event time \<tau>_res (get_state res') , Femto_VHDL_raw.add_to_beh2 (get_state res') (get_beh res') time def, def  \<turnstile> <nand4 , \<tau>_res
           (next_time time \<tau>_res := 0)> \<longrightarrow>\<^sub>c  \<tau>_res (next_time time \<tau>_res := 0)\<close> 
              by (smt b_conc_exec_deterministic less_le_not_le)
            hence "get_beh res = Femto_VHDL_raw.add_to_beh2 (next_state time \<tau>_res (get_state res')) (Femto_VHDL_raw.add_to_beh2 (get_state res') (get_beh res') time def) (next_time time \<tau>_res) def"
              by auto }
          ultimately have gb_res: "get_beh res = Femto_VHDL_raw.add_to_beh2 (next_state time \<tau>_res (get_state res')) (Femto_VHDL_raw.add_to_beh2 (get_state res') (get_beh res') time def) (next_time time \<tau>_res) def"
              by auto
          have " (next_time time \<tau>_res) \<le> i"
            using \<open>next_time time \<tau>_res < Suc i\<close> less_Suc_eq_le by blast
          have "signal_of (def C) (get_beh res) C i = (next_state time \<tau>_res (get_state res')) C"
            unfolding gb_res
            apply (intro signal_of_add_to_beh2'[OF `next_time time \<tau>_res \<le> i`] )
            by (smt Femto_VHDL_raw.add_to_beh2_def \<open>next_time time \<tau>_res = time\<close> b_simulate_fin_preserves_hist bigstep2_pre fun_upd_other nat_neq_iff trans_removal zero_fun_def)
          also have "... = the (\<tau>_res time C)"
            unfolding next_state_def `next_time time \<tau>_res = time` Let_def 
            by (metis \<open>\<tau>_res time C \<noteq> 0\<close> comp_apply domIff override_on_apply_in zero_option_def)
          also have "... = x'"
            by (simp add: \<open>\<tau>_res time C = Some x'\<close>)
          finally have "signal_of (def C) (get_beh res) C i = x'"
            by auto
          have "signal_of (def A) \<tau> A i  = signal_of (def A) \<tau>' A i"
            using init'_modifies_local_strongest[OF `init' 0 def {} 0 def nand4 \<tau> \<tau>'` `A \<notin> set (signals_from nand4)`]
            using \<open>trans_post_raw C x (def C) \<tau> 0 0 = \<tau>'\<close> signal_of_trans_post by fastforce
          also have "... = signal_of (\<sigma>' A) \<tau>' A i"
            by (metis \<open>inf_time (to_trans_raw_sig \<tau>) A i = Some time1\<close> \<open>trans_post_raw C x (def C) \<tau> 0 0 = \<tau>'\<close> comp_apply option.simps(5) sig.distinct(3) signal_of_trans_post to_signal_def)
          also have "... = signal_of (\<sigma>' A) (\<tau>'(t':=0)) A i"
            by (smt \<open>next_state 0 \<tau>' def = \<sigma>'\<close> \<open>next_time 0 \<tau>' = t'\<close> comp_apply next_state_def next_time_at_least2 override_on_apply_in signal_of_rem_curr_trans_at_t)
          also have "... = signal_of (get_state res' A) (get_trans res') A i"
            using bau_signal_of[OF bigstep2_pre `A \<notin> set (signals_from nand4)` _ trans_removal] `time < Suc i`
            using less_Suc_eq_le by blast
          also have "... = get_state res' A"
            by (smt \<open>A \<notin> set (signals_from nand4)\<close> \<open>Suc i \<le> next_time (next_time time \<tau>_res)
            (\<tau>_res(next_time time \<tau>_res := 0))\<close> \<open>\<tau>_res time A = 0\<close> \<open>get_trans res' time = 0\<close>
            \<open>next_time time \<tau>_res = time\<close> \<open>time , get_state res' , get_beh' res' , get_beh res', def
            \<turnstile> <nand4 , get_trans res'> \<longrightarrow>\<^sub>c \<tau>_res\<close> antisym_conv2 b_conc_exec_modifies_local_strongest
            dual_order.strict_trans2 fun_upd_other lessI next_time_at_least2 signal_of_def
            signal_of_suc_sig)
          finally have "signal_of (def A) \<tau> A i = get_state res' A"
            by auto
          have "signal_of (def B) \<tau> B i  = signal_of (def B) \<tau>' B i"
            using init'_modifies_local_strongest[OF `init' 0 def {} 0 def nand4 \<tau> \<tau>'` `B \<notin> set (signals_from nand4)`]
            using \<open>trans_post_raw C x (def C) \<tau> 0 0 = \<tau>'\<close> signal_of_trans_post by fastforce
          also have "... = signal_of (\<sigma>' B) \<tau>' B i"
            by (metis \<open>inf_time (to_trans_raw_sig \<tau>) B i = Some time2\<close> \<open>trans_post_raw C x (def C) \<tau> 0 0 = \<tau>'\<close> comp_apply inf_time_trans_post option.simps(5) sig.distinct(5) to_signal_def)
          also have "... = signal_of (\<sigma>' B) (\<tau>'(t':=0)) B i"
            by (smt \<open>next_state 0 \<tau>' def = \<sigma>'\<close> \<open>next_time 0 \<tau>' = t'\<close> comp_apply next_state_def next_time_at_least2 override_on_apply_in signal_of_rem_curr_trans_at_t)
          also have "... = signal_of (get_state res' B) (get_trans res') B i"
            using bau_signal_of[OF bigstep2_pre `B \<notin> set (signals_from nand4)` _ trans_removal] `time < Suc i`
            using less_Suc_eq_le by blast
          also have "... = get_state res' B"
            by (smt \<open>B \<notin> set (signals_from nand4)\<close> \<open>Suc i \<le> next_time (next_time time \<tau>_res)
            (\<tau>_res(next_time time \<tau>_res := 0))\<close> \<open>\<tau>_res time B = 0\<close> \<open>get_trans res' time = 0\<close>
            \<open>next_time time \<tau>_res = time\<close> \<open>time , get_state res' , get_beh' res' , get_beh res', def
            \<turnstile> <nand4 , get_trans res'> \<longrightarrow>\<^sub>c \<tau>_res\<close> antisym_conv2 b_conc_exec_modifies_local_strongest
            dual_order.strict_trans2 fun_upd_other le_Suc_eq less_Suc_eq_le next_time_at_least2
            signal_of_def)
          finally have "signal_of (def B) \<tau> B i = get_state res' B"
            by auto
          have "time , get_state res' , get_beh' res' , get_beh res', def  \<turnstile> Bsig A \<longrightarrow>\<^sub>b Bv (bval_of (get_state res' A))"
            by (smt \<open>0 , def , {} , 0, def \<turnstile> Bnand (Bsig A) (Bsig B) \<longrightarrow>\<^sub>b x\<close> \<open>signal_of (def A) \<tau> A i =
            get_state res' A\<close> \<open>x = Bv (\<not> (bval_of (def A) \<and> bval_of (def B)))\<close> assms(4) assms(6)
            beval_cases(1) beval_cases(9) beval_raw.intros(1) signal_of_preserve_well_typedness
            styping_def ty.simps(3) type_of.simps(1) type_of.simps(2) val.exhaust_sel)
          moreover have "time , get_state res' , get_beh' res' , get_beh res', def  \<turnstile> Bsig B \<longrightarrow>\<^sub>b Bv (bval_of (get_state res' B))"
            by (smt \<open>time , get_state res' , get_beh' res' , get_beh res', def \<turnstile> Bnand (Bsig A) (Bsig B)
            \<longrightarrow>\<^sub>b x'\<close> \<open>time , get_state res' , get_beh' res' , get_beh res', def \<turnstile> Bsig A \<longrightarrow>\<^sub>b Bv (bval_of
            (get_state res' A))\<close> beval_cases(9) beval_raw.intros(1) beval_raw_deterministic
            val.distinct(1) val.exhaust_sel)
          ultimately have "x' = Bv (\<not> (bval_of (get_state res' A) \<and> bval_of (get_state res' B)))"
            using beval_cases(9)[OF `time , get_state res' , get_beh' res' , get_beh res', def  \<turnstile> Bnand (Bsig A) (Bsig B) \<longrightarrow>\<^sub>b x'`]
            by (smt beval_cases(1) val.distinct(1))
          hence ?thesis
            using \<open>signal_of (def A) \<tau> A i = get_state res' A\<close> \<open>signal_of (def B) \<tau> B i = get_state res' B\<close> \<open>signal_of (def C) (get_beh res) C i = x'\<close> 
            by auto }
        ultimately have ?thesis
          by auto }
      ultimately have ?thesis
        by auto }
    ultimately show ?thesis
      using nat_less_le by blast
  next
    case either
    moreover
    { assume "inf_time (to_trans_raw_sig \<tau>) A i \<noteq> None \<and> inf_time (to_trans_raw_sig \<tau>) B i = None"
      then obtain time where "inf_time (to_trans_raw_sig \<tau>) A i = Some time" and "inf_time (to_trans_raw_sig \<tau>) B i = None"
        by blast
      have "next_time 0 \<tau>' \<le> time"
      proof -
        have "next_time 0 \<tau>' = (LEAST n. dom (\<tau>' n) \<noteq> {})"
          unfolding next_time_def using \<open>\<tau>' \<noteq> 0\<close> by auto
        have "\<exists>n. dom (\<tau>' n) \<noteq> {}"
          using \<open>\<tau>' \<noteq> 0\<close> unfolding dom_def zero_fun_def zero_option_def 
          by fastforce
        have "inf_time (to_trans_raw_sig \<tau>) A i = inf_time (to_trans_raw_sig \<tau>') A i"
          using \<open>trans_post_raw C x (def C) \<tau> 0 0 = \<tau>'\<close> inf_time_trans_post by fastforce
        hence "dom (\<tau>' time) \<noteq> {}"
          using \<open>inf_time (to_trans_raw_sig \<tau>) A i  = Some time\<close> unfolding dom_def 
        proof -
          have "\<exists>s. to_trans_raw_sig \<tau>' s time \<noteq> None"
            by (metis Femto_VHDL_raw.keys_def \<open>inf_time (to_trans_raw_sig \<tau>) A i = Some time\<close> \<open>inf_time (to_trans_raw_sig \<tau>) A i = inf_time (to_trans_raw_sig \<tau>') A i\<close> domIff dom_def inf_time_some_exists zero_option_def)
          then show "{s. \<tau>' time s \<noteq> None} \<noteq> {}"
            by (simp add: to_trans_raw_sig_def)
        qed
        hence "(LEAST n. dom (\<tau>' n) \<noteq> {}) \<le> time"
          using Least_le by auto
        thus "next_time 0 \<tau>' \<le> time"
          using \<open>next_time 0 \<tau>' = (LEAST n. dom (\<tau>' n) \<noteq> {})\<close> by linarith
      qed    
      have "time < Suc i"
        using \<open>inf_time (to_trans_raw_sig \<tau>) A i = Some time\<close>  inf_time_at_most by fastforce    
      have "\<exists>res'. time, t' , \<sigma>' , \<gamma>' , 0, def \<turnstile> <nand4 , \<tau>'(t' := 0)> \<leadsto> res' \<and> Suc i, time , get_state res' , get_beh' res' , get_beh res', def \<turnstile> <nand4 , get_trans res'> \<leadsto> res"
        using split_b_simulate_fin[OF bigstep \<open>next_time 0 \<tau>' \<le>time\<close>[unfolded \<open>next_time 0 \<tau>' = t'\<close>] _ trans_removal conc_stmt_wf_nand4]  \<open>time < Suc i\<close>
        by (meson less_or_eq_imp_le zero_fun_def)
      then obtain res' where bigstep2_pre: "time, t' , \<sigma>' , \<gamma>' , 0, def \<turnstile> <nand4 , \<tau>'(t' := 0)> \<leadsto> res'"
        and bigstep2: "Suc i, time , get_state res' , get_beh' res' , get_beh res', def \<turnstile> <nand4 , get_trans res'> \<leadsto> res"
        by auto
      have "A \<notin> set (signals_from nand4)" and "B \<notin> set (signals_from nand4)"
        unfolding nand4_def by auto
      have "t' < time \<or> t' = time"
        using bau bigstep2_pre by blast
      moreover 
      { assume "t' < time"
        moreover have "\<tau>' time A = \<tau> time A" and "\<tau>' time B = \<tau> time B"
          unfolding \<tau>'_def trans_post_raw_def post_raw_def preempt_raw_def by auto
        moreover have "\<tau> time A \<noteq> 0 \<and> \<tau> time B = 0"
          using \<open>inf_time (to_trans_raw_sig \<tau>) A i = Some time\<close>  \<open>inf_time (to_trans_raw_sig \<tau>) B i = None\<close>
          by (metis Femto_VHDL_raw.keys_def domIff dom_def inf_time_noneE2 inf_time_some_exists
          to_trans_raw_sig_def zero_option_def)
        ultimately have "(\<tau>'(t' := 0)) time A \<noteq> 0 \<and> (\<tau>'(t' := 0)) time B = 0"
          by auto
        hence "A \<notin> set (signals_from nand4)"
          unfolding nand4_def by auto
        have "non_stuttering (to_trans_raw_sig \<tau>') def A"
          using init'_preserves_non_stuttering[OF `init' 0 def {} 0 def nand4 \<tau> \<tau>'` _ _ conc_stmt_wf_nand4] assms(7)
          by blast
        hence "non_stuttering (to_trans_raw_sig (\<tau>'(t' := 0))) \<sigma>' A"
          using non_stuttering_next \<open>next_state 0 \<tau>' def = \<sigma>'\<close> \<open>next_time 0 \<tau>' = t'\<close> by fastforce
        hence "get_event res' \<noteq>  {}"
          using get_event_never_empty'[OF bigstep2_pre \<open>A \<notin> set (signals_from nand4)\<close> _ _ _ trans_removal conc_stmt_wf_nand4]
          \<open>t' < time\<close> \<open>(\<tau>'(t' := 0)) time A \<noteq> 0 \<and> (\<tau>'(t' := 0)) time B = 0\<close> by blast
        have "\<not> disjnt {A, B} (get_event res')"
          using get_event_never_empty[OF bigstep2_pre \<open>A \<notin> set (signals_from nand4)\<close> _ _ _ trans_removal conc_stmt_wf_nand4]
          using \<open>t' < time\<close> \<open>non_stuttering (to_trans_raw_sig (\<tau>'(t' := 0))) \<sigma>' A\<close>  
          using \<open>(\<tau>'(t' := 0)) time A \<noteq> 0 \<and> (\<tau>'(t' := 0)) time B = 0\<close> by fastforce
        hence "get_event res' \<noteq>  {} \<and> \<not> disjnt {A, B} (get_event res')"
          by auto }
      moreover 
      { assume "t' = time"
        hence "res' = (time, \<sigma>', \<gamma>', 0, \<tau>'(t' := 0))"
          using bau[OF bigstep2_pre] by auto
        hence "get_event res' = \<gamma>'"
          by auto
        also have "... = next_event 0 \<tau>' def"
          using \<open>next_event 0 \<tau>' def = \<gamma>'\<close> by auto
        also have "... = {sig. def sig \<noteq> next_state 0 \<tau>' def sig} "
          unfolding next_event_alt_def by auto
        also have "... \<noteq> {}"
        proof -
          have "\<tau>' time A = \<tau> time A" and "\<tau>' time B = \<tau> time B"
            unfolding \<tau>'_def trans_post_raw_def post_raw_def preempt_raw_def by auto
          moreover have "\<tau> time A \<noteq> 0 \<and> \<tau> time B = 0"
            using \<open>inf_time (to_trans_raw_sig \<tau>) A i = Some time\<close> \<open>inf_time (to_trans_raw_sig \<tau>) B i = None\<close> 
            by (metis Femto_VHDL_raw.keys_def domIff dom_def inf_time_noneE2 inf_time_some_exists
            to_trans_raw_sig_def zero_option_def)
          ultimately have "\<tau>' time A \<noteq> 0" and " \<tau>' time B =0"
            by auto
          have  "Femto_VHDL_raw.keys (to_trans_raw_sig \<tau> A) \<noteq> {}"
            using \<open>inf_time (to_trans_raw_sig \<tau>) A i = Some time\<close> inf_time_some_exists by force
          moreover have *: "(LEAST k. k \<in> Femto_VHDL_raw.keys (to_trans_raw_sig \<tau> A)) = time"
          proof (rule Least_equality)
            show " time \<in> Femto_VHDL_raw.keys (to_trans_raw_sig \<tau> A)"
              by (meson \<open>inf_time (to_trans_raw_sig \<tau>) A i = Some time\<close> inf_time_some_exists)
          next
            { fix y 
              assume "y < time"
              assume "y \<in> Femto_VHDL_raw.keys (to_trans_raw_sig \<tau> A)"
              hence "\<tau> y A \<noteq> 0"
                unfolding Femto_VHDL_raw.keys_def to_trans_raw_sig_def by auto
              hence "\<tau>' y A \<noteq> 0"
                by (metis \<open>trans_post_raw C x (def C) \<tau> 0 0 = \<tau>'\<close> sig.distinct(3) sig.distinct(5) to_trans_raw_sig_def trans_post_raw_diff_sig)
              with `y < time` have False
                unfolding `t' = time`[THEN sym] `next_time  0 \<tau>' = t'`[THEN sym] 
                by (simp add: next_time_at_least2 zero_fun_def) }
            thus "\<And>y. y \<in> Femto_VHDL_raw.keys (to_trans_raw_sig \<tau> A) \<Longrightarrow> time \<le> y"
              using not_less by blast
          qed
          moreover have "the (to_trans_raw_sig \<tau> A (LEAST k. k \<in> Femto_VHDL_raw.keys (to_trans_raw_sig \<tau> A))) = next_state 0 \<tau>' def A"
            unfolding * next_state_def 
            by (metis \<open>\<tau>' time A = \<tau> time A\<close> \<open>\<tau>' time A \<noteq> 0\<close> \<open>next_time 0 \<tau>' = t'\<close> \<open>t' = time\<close> comp_apply domIff override_on_apply_in to_trans_raw_sig_def zero_option_def) 
          ultimately show ?thesis
            using assms(7)[unfolded non_stuttering_def] by auto
        qed
        finally have "get_event res' \<noteq>  {}"
          by auto
        have "\<not> disjnt {A, B} (get_event res')"
        proof -
          have "\<tau>' time A = \<tau> time A" and "\<tau>' time B = \<tau> time B"
            unfolding \<tau>'_def trans_post_raw_def post_raw_def preempt_raw_def by auto
          moreover have "\<tau> time A \<noteq> 0 \<and> \<tau> time B = 0"
            using \<open>inf_time (to_trans_raw_sig \<tau>) A i = Some time\<close> \<open>inf_time (to_trans_raw_sig \<tau>) B i = None\<close> 
            by (metis Femto_VHDL_raw.keys_def domIff dom_def inf_time_noneE2 inf_time_some_exists to_trans_raw_sig_def zero_option_def)
          ultimately have "\<tau>' time A \<noteq> 0 " and " \<tau>' time B = 0"
            by auto
          moreover have "\<tau>' time A = \<tau> time A"
            using \<open>\<tau>' time A = \<tau> time A\<close> \<open>\<tau>' time B = \<tau> time B\<close> calculation(2) by blast
          moreover have  "Femto_VHDL_raw.keys (to_trans_raw_sig \<tau> A) \<noteq> {}"
            using \<open>inf_time (to_trans_raw_sig \<tau>) A i = Some time\<close> \<open>inf_time (to_trans_raw_sig \<tau>) B i = None\<close> calculation(2) inf_time_some_exists by force
          moreover have *: "(LEAST k. k \<in> Femto_VHDL_raw.keys (to_trans_raw_sig \<tau> A)) = time"
          proof (rule Least_equality)
            show " time \<in> Femto_VHDL_raw.keys (to_trans_raw_sig \<tau> A)"
              by (metis Femto_VHDL_raw.keys_def calculation(1) calculation(3) domIff dom_def to_trans_raw_sig_def zero_option_def)
          next
            { fix y 
              assume "y < time"
              assume "y \<in> Femto_VHDL_raw.keys (to_trans_raw_sig \<tau> A)"
              hence "\<tau> y A \<noteq> 0"
                unfolding Femto_VHDL_raw.keys_def to_trans_raw_sig_def by auto
              hence "\<tau>' y A \<noteq> 0"
                by (metis \<open>trans_post_raw C x (def C) \<tau> 0 0 = \<tau>'\<close> calculation(2) sig.distinct(3) sig.distinct(5) to_trans_raw_sig_def trans_post_raw_diff_sig)
              with `y < time` have False
                unfolding `t' = time`[THEN sym] `next_time  0 \<tau>' = t'`[THEN sym] 
                by (simp add: next_time_at_least2 zero_fun_def) }
            thus "\<And>y. y \<in> Femto_VHDL_raw.keys (to_trans_raw_sig \<tau> A) \<Longrightarrow> time \<le> y"
              using not_less by blast
          qed
          moreover have "the (to_trans_raw_sig \<tau> A (LEAST k. k \<in> Femto_VHDL_raw.keys (to_trans_raw_sig \<tau> A))) = next_state 0 \<tau>' def A"
            unfolding * next_state_def 
            by (metis \<open>next_time 0 \<tau>' = t'\<close> \<open>t' = time\<close> calculation(1) calculation(3) comp_apply domIff override_on_apply_in to_trans_raw_sig_def zero_option_def) 
          ultimately show ?thesis
            by (metis (full_types) \<open>get_beh' res' = \<gamma>'\<close> \<open>next_event 0 \<tau>' def = \<gamma>'\<close> assms(7) disjnt_insert1 next_state_fixed_point non_stuttering_def)
        qed 
        hence "get_event res' \<noteq> {} \<and> \<not> disjnt {A, B} (get_event res')"
          using \<open>get_beh' res' \<noteq> {}\<close> by blast }
      ultimately have "get_event res' \<noteq> {} \<and> \<not> disjnt {A, B} (get_event res')"
        by auto
      hence " \<not> quiet (get_trans res') (get_event res')" and "\<not> disjnt {A, B} (get_event res')"
        by (simp add: quiet_def)+
      then obtain \<tau>_res where "time, get_state res', get_event res', get_beh res', def \<turnstile> <nand4, get_trans res'> \<longrightarrow>\<^sub>c \<tau>_res"
        using bau[OF bigstep2]  using \<open>time < Suc i\<close> by force
      have "next_time time \<tau>_res \<le> Suc i \<or> Suc i < next_time time \<tau>_res"
        by auto
      moreover
      { assume "Suc i < next_time time \<tau>_res"
        hence " res = (Suc i, get_state res', {}, Femto_VHDL_raw.add_to_beh2 (get_state res') (get_beh res') time def, \<tau>_res) "
          using bau[OF bigstep2] `\<not> quiet (get_trans res') (get_event res')` `time < Suc i` 
          by (smt \<open>time , get_state res' , get_beh' res' , get_beh res', def \<turnstile> <nand4 , get_trans
          res'> \<longrightarrow>\<^sub>c \<tau>_res\<close> b_conc_exec_deterministic less_irrefl_nat not_le)
        hence gb_res: "get_beh res =  Femto_VHDL_raw.add_to_beh2 (get_state res') (get_beh res') time def"
          by auto
        have "time \<le> i"
          using \<open>time < Suc i\<close> less_Suc_eq_le by blast
        have "\<forall>n>time. get_beh res' n C = 0"
          by (metis b_simulate_fin_preserves_hist bigstep2_pre trans_removal zero_fun_def)
        hence "signal_of (def C) (get_beh res) C i = get_state res' C"
          using signal_of_add_to_beh2'[OF `time \<le> i` ] unfolding gb_res by auto
        have "signal_of (def A) \<tau> A i  = signal_of (def A) \<tau>' A i"
          using init'_modifies_local_strongest[OF `init' 0 def {} 0 def nand4 \<tau> \<tau>'` `A \<notin> set (signals_from nand4)`]
          using \<open>trans_post_raw C x (def C) \<tau> 0 0 = \<tau>'\<close> signal_of_trans_post by fastforce
        also have "... = signal_of (\<sigma>' A) \<tau>' A i"
          by (metis \<open>inf_time (to_trans_raw_sig \<tau>) A i = Some time\<close> \<open>trans_post_raw C x (def C) \<tau> 0 0 = \<tau>'\<close> comp_apply option.simps(5) sig.distinct(3) signal_of_trans_post to_signal_def)
        also have "... = signal_of (\<sigma>' A) (\<tau>'(t':=0)) A i"
          by (smt \<open>next_state 0 \<tau>' def = \<sigma>'\<close> \<open>next_time 0 \<tau>' = t'\<close> comp_apply next_state_def next_time_at_least2 override_on_apply_in signal_of_rem_curr_trans_at_t)
        also have "... = signal_of (get_state res' A) (get_trans res') A i"
          using bau_signal_of[OF bigstep2_pre `A \<notin> set (signals_from nand4)` `time \<le> i` trans_removal]
          by blast
        also have "... = get_state res' A"
          by (rule signal_of_def)
             (metis (no_types, lifting) Suc_lessD \<open>A \<notin> set (signals_from nand4)\<close> \<open>Suc i < next_time
             time \<tau>_res\<close> \<open>time , get_state res' , get_beh' res' , get_beh res', def \<turnstile> <nand4 ,
             get_trans res'> \<longrightarrow>\<^sub>c \<tau>_res\<close> antisym_conv2 b_conc_exec_modifies_local_strongest
             dual_order.strict_trans next_time_at_least2 zero_fun_def)
        finally have "signal_of (def A) \<tau> A i = get_state res' A"
          by auto
        have "signal_of (def B) \<tau> B i  = def B"
          using `inf_time (to_trans_raw_sig \<tau>) B i = None` 
          by (simp add: to_signal_def)
        also have "... = \<sigma>' B"
        proof -
          have "B \<notin> (dom (\<tau>' (next_time 0 \<tau>')))"
            using \<open>inf_time (to_trans_raw_sig \<tau>) B i = None\<close>
            using init'_modifies_local_strongest[OF `init' 0 def {} 0 def nand4 \<tau> \<tau>'` `B \<notin> set (signals_from nand4)`]          
            by (metis \<open>\<And>thesis. (\<And>time. \<lbrakk>inf_time (to_trans_raw_sig \<tau>) A i = Some time; inf_time
            (to_trans_raw_sig \<tau>) B i = None\<rbrakk> \<Longrightarrow> thesis) \<Longrightarrow> thesis\<close> \<open>next_time 0 \<tau>' = t'\<close> \<open>t' < time \<or> t'
            = time\<close> \<open>time \<le> i\<close> domIff dom_def inf_time_noneE2 not_le order.strict_trans
            to_trans_raw_sig_def zero_option_def)
          thus ?thesis
            unfolding `next_state 0 \<tau>' def = \<sigma>'`[THEN sym] next_state_def Let_def  by simp
        qed
        also have "... = get_state res' B"
        proof -
          have "inf_time (to_trans_raw_sig (\<tau>'(t' := 0))) B time = None"
            unfolding inf_time_none_iff[THEN sym]
          proof 
            { fix x 
              assume " x \<in> dom (to_trans_raw_sig (\<tau>'(t' := 0)) B)"
              hence "(\<tau>'(t' := 0)) x B \<noteq> None"
                unfolding dom_def to_trans_raw_sig_def by auto
              hence "x \<noteq> t'"
                unfolding fun_upd_def zero_fun_def zero_option_def by auto
              assume "x \<le> time"
              have "(\<tau>'(t' := 0)) x B = \<tau>' x B"
                using `x \<noteq> t'` by auto
              also have "... = \<tau> x B"
                using init'_modifies_local_strongest[OF `init' 0 def {} 0 def nand4 \<tau> \<tau>'` `B \<notin> set (signals_from nand4)`]          
                by auto
              also have "... = None"
                using \<open>inf_time (to_trans_raw_sig \<tau>) B i = None\<close> \<open>time \<le> i\<close> 
                by (metis \<open>x \<le> time\<close> inf_time_noneE2 le_less_trans not_le to_trans_raw_sig_def zero_option_def) 
              finally have "False"
                using \<open>(\<tau>'(t' := 0)) x B \<noteq> None\<close> by blast }
            thus "\<And>x. x \<in> dom (to_trans_raw_sig (\<tau>'(t' := 0)) B) \<Longrightarrow> time < x"
              using le_less_linear by blast
          qed
          thus ?thesis
            using get_state_b_simulate_fin_inf_none[OF bigstep2_pre `B \<notin> set (signals_from nand4)`] 
            by auto
        qed
        finally have "signal_of (def B) \<tau> B i = get_state res' B"
          by auto
        have "time , get_state res' , get_event res' , get_beh res', def  \<turnstile> <Bassign_trans C (Bnand (Bsig A) (Bsig B)) 0 , get_trans res'> \<longrightarrow>\<^sub>s \<tau>_res"
          using conc_cases(1)[OF `time, get_state res', get_event res', get_beh res', def \<turnstile> <nand4, get_trans res'> \<longrightarrow>\<^sub>c \<tau>_res`[unfolded nand4_def]]
          `\<not> disjnt {A, B} (get_event res')` by auto
        obtain x' where " time , get_state res' , get_beh' res' , get_beh res', def  \<turnstile> Bnand (Bsig A) (Bsig B) \<longrightarrow>\<^sub>b x'" and 
          \<tau>_res_def: " trans_post_raw C x' (get_state res' C) (get_trans res') time 0 = \<tau>_res"
          using seq_cases_trans[OF `time , get_state res' , get_event res' , get_beh res', def  \<turnstile> <Bassign_trans C (Bnand (Bsig A) (Bsig B)) 0 , get_trans res'> \<longrightarrow>\<^sub>s \<tau>_res`]
          by blast
        have "time , get_state res' , get_beh' res' , get_beh res', def  \<turnstile> Bsig A \<longrightarrow>\<^sub>b Bv (bval_of (get_state res' A))"
          by (smt \<open>0 , def , {} , 0, def \<turnstile> Bnand (Bsig A) (Bsig B) \<longrightarrow>\<^sub>b x\<close> \<open>signal_of (def A) \<tau> A i =
          get_state res' A\<close> \<open>x = Bv (\<not> (bval_of (def A) \<and> bval_of (def B)))\<close> assms(4) assms(6)
          beval_cases(1) beval_cases(9) beval_raw.intros(1) signal_of_preserve_well_typedness
          styping_def ty.simps(3) type_of.simps(1) type_of.simps(2) val.exhaust_sel)
        moreover have "time , get_state res' , get_beh' res' , get_beh res', def  \<turnstile> Bsig B \<longrightarrow>\<^sub>b Bv (bval_of (get_state res' B))"
          by (smt \<open>time , get_state res' , get_beh' res' , get_beh res', def \<turnstile> Bnand (Bsig A) (Bsig B)
          \<longrightarrow>\<^sub>b x'\<close> \<open>time , get_state res' , get_beh' res' , get_beh res', def \<turnstile> Bsig A \<longrightarrow>\<^sub>b Bv (bval_of
          (get_state res' A))\<close> beval_cases(9) beval_raw.intros(1) beval_raw_deterministic
          val.distinct(1) val.exhaust_sel)
        ultimately have "x' = Bv (\<not> (bval_of (get_state res' A) \<and> bval_of (get_state res' B)))"
          using beval_cases(9)[OF `time , get_state res' , get_beh' res' , get_beh res', def  \<turnstile> Bnand (Bsig A) (Bsig B) \<longrightarrow>\<^sub>b x'`]
          by (smt beval_cases(1) val.distinct(1))
        have "\<not> post_necessary_raw 0 (get_trans res') time C x' (get_state res' C)"
        proof (rule ccontr)
          assume "\<not> \<not> post_necessary_raw 0 (get_trans res') time C x' (get_state res' C)"
          hence "post_necessary_raw 0 (get_trans res') time C x' (get_state res' C)"
            by auto
          hence "\<tau>_res time C = post_raw C x' (get_trans res') (time + 0) time C"
            unfolding \<tau>_res_def[THEN sym] trans_post_raw_def by auto
          hence "next_time time \<tau>_res = time"
            by (metis (no_types, lifting) \<open>Suc i < next_time time \<tau>_res\<close> \<open>time < Suc i\<close>
            add.right_neutral dual_order.strict_trans fun_upd_same next_time_at_least2
            option.distinct(1) post_raw_def zero_fun_def zero_option_def)
          thus "False"
            using `Suc i < next_time time \<tau>_res`  using \<open>time < Suc i\<close> by linarith
        qed
        moreover have "\<not> (\<exists>i\<le>time + 0 - 1. get_trans res' i C = Some x')"
          using b_simulate_fin_preserve_trans_removal[OF bigstep2_pre trans_removal] 
          by (metis (no_types, hide_lams) Suc_diff_1 \<open>t' < time \<or> t' = time\<close> add.right_neutral
          b_simulate_fin.intros(4) b_simulate_fin_deterministic bigstep2_pre comp_eq_dest_lhs
          diff_le_self fun_upd_same le_imp_less_Suc not_gr_zero not_le not_less_zero
          option.distinct(1) snd_conv zero_fun_def zero_option_def)
        ultimately have "x' = get_state res' C"
          unfolding post_necessary_raw_correctness by blast
        hence "bval_of (get_state res' C) \<longleftrightarrow> \<not> (bval_of (get_state res' A) \<and> bval_of (get_state res' B))"
          using `x' = Bv (\<not> (bval_of (get_state res' A) \<and> bval_of (get_state res' B)))`
          using val.sel(1) by presburger
        hence ?thesis
          using `signal_of (def A) \<tau> A i = get_state res' A` `signal_of (def B) \<tau> B i = get_state res' B`
          `signal_of (def C) (get_beh res) C i = get_state res' C` by auto }
      moreover
      { assume "next_time time \<tau>_res = Suc i"
        hence bigstep3: "Suc i, next_time time \<tau>_res , next_state time \<tau>_res (get_state res') , next_event time \<tau>_res (get_state res') , Femto_VHDL_raw.add_to_beh2 (get_state res') (get_beh res') time def, def \<turnstile> <nand4 , \<tau>_res (next_time time \<tau>_res := 0)> \<leadsto> res"
          using bau[OF bigstep2] 
          by (smt \<open>\<not> quiet (get_trans res') (get_beh' res')\<close> \<open>time , get_state res' , get_beh' res' ,
          get_beh res', def \<turnstile> <nand4 , get_trans res'> \<longrightarrow>\<^sub>c \<tau>_res\<close> \<open>time < Suc i\<close> bigstep2
          calculation(1) case_bau less_irrefl_nat)
        have "res = (Suc i, next_state time \<tau>_res (get_state res'), next_event time \<tau>_res (get_state res'), Femto_VHDL_raw.add_to_beh2 (get_state res') (get_beh res') time def, \<tau>_res (next_time time \<tau>_res := 0))"
          using bau[OF bigstep3] `next_time time \<tau>_res = Suc i` by auto
        hence gb_res: "get_beh res = Femto_VHDL_raw.add_to_beh2 (get_state res') (get_beh res') time def"
          by auto
        have "time \<le> i"
          using \<open>time < Suc i\<close> less_Suc_eq_le by blast
        have "\<forall>n>time. get_beh res' n C = 0"
          by (metis b_simulate_fin_preserves_hist bigstep2_pre trans_removal zero_fun_def)
        hence "signal_of (def C) (get_beh res) C i = get_state res' C"
          using signal_of_add_to_beh2'[OF `time \<le> i` ] unfolding gb_res by auto
        have "signal_of (def A) \<tau> A i  = signal_of (def A) \<tau>' A i"
          using init'_modifies_local_strongest[OF `init' 0 def {} 0 def nand4 \<tau> \<tau>'` `A \<notin> set (signals_from nand4)`]
          using \<open>trans_post_raw C x (def C) \<tau> 0 0 = \<tau>'\<close> signal_of_trans_post by fastforce
        also have "... = signal_of (\<sigma>' A) \<tau>' A i"
          by (metis \<open>inf_time (to_trans_raw_sig \<tau>) A i = Some time\<close> \<open>trans_post_raw C x (def C) \<tau> 0 0 = \<tau>'\<close> comp_apply option.simps(5) sig.distinct(3) signal_of_trans_post to_signal_def)
        also have "... = signal_of (\<sigma>' A) (\<tau>'(t':=0)) A i"
          by (smt \<open>next_state 0 \<tau>' def = \<sigma>'\<close> \<open>next_time 0 \<tau>' = t'\<close> comp_apply next_state_def next_time_at_least2 override_on_apply_in signal_of_rem_curr_trans_at_t)
        also have "... = signal_of (get_state res' A) (get_trans res') A i"
          using bau_signal_of[OF bigstep2_pre `A \<notin> set (signals_from nand4)` `time \<le> i` trans_removal]
          by blast
        also have "... = get_state res' A"
          by (metis (no_types, lifting) \<open>A \<notin> set (signals_from nand4)\<close> \<open>next_time time \<tau>_res = Suc i\<close> \<open>time , get_state res' , get_beh' res' , get_beh res', def \<turnstile> <nand4 , get_trans res'> \<longrightarrow>\<^sub>c \<tau>_res\<close> b_conc_exec_modifies_local_strongest dual_order.strict_trans2 lessI next_time_at_least2 signal_of_def zero_fun_def)
        finally have "signal_of (def A) \<tau> A i = get_state res' A"
          by auto
        have "signal_of (def B) \<tau> B i  = def B"
          using `inf_time (to_trans_raw_sig \<tau>) B i = None` 
          by (simp add: to_signal_def)
        also have "... = \<sigma>' B"
        proof -
          have "B \<notin> (dom (\<tau>' (next_time 0 \<tau>')))"
            using \<open>inf_time (to_trans_raw_sig \<tau>) B i = None\<close>
            using init'_modifies_local_strongest[OF `init' 0 def {} 0 def nand4 \<tau> \<tau>'` `B \<notin> set (signals_from nand4)`]          
            by (metis \<open>\<And>thesis. (\<And>time. \<lbrakk>inf_time (to_trans_raw_sig \<tau>) A i = Some time; inf_time
            (to_trans_raw_sig \<tau>) B i = None\<rbrakk> \<Longrightarrow> thesis) \<Longrightarrow> thesis\<close> \<open>next_time 0 \<tau>' = t'\<close> \<open>t' < time \<or> t'
            = time\<close> \<open>time \<le> i\<close> domIff dom_def inf_time_noneE2 not_le order.strict_trans
            to_trans_raw_sig_def zero_option_def)
          thus ?thesis
            unfolding `next_state 0 \<tau>' def = \<sigma>'`[THEN sym] next_state_def Let_def  by simp
        qed
        also have "... = get_state res' B"
        proof -
          have "inf_time (to_trans_raw_sig (\<tau>'(t' := 0))) B time = None"
            unfolding inf_time_none_iff[THEN sym]
          proof 
            { fix x 
              assume " x \<in> dom (to_trans_raw_sig (\<tau>'(t' := 0)) B)"
              hence "(\<tau>'(t' := 0)) x B \<noteq> None"
                unfolding dom_def to_trans_raw_sig_def by auto
              hence "x \<noteq> t'"
                unfolding fun_upd_def zero_fun_def zero_option_def by auto
              assume "x \<le> time"
              have "(\<tau>'(t' := 0)) x B = \<tau>' x B"
                using `x \<noteq> t'` by auto
              also have "... = \<tau> x B"
                using init'_modifies_local_strongest[OF `init' 0 def {} 0 def nand4 \<tau> \<tau>'` `B \<notin> set (signals_from nand4)`]          
                by auto
              also have "... = None"
                using \<open>inf_time (to_trans_raw_sig \<tau>) B i = None\<close> \<open>time \<le> i\<close> 
                by (metis \<open>x \<le> time\<close> inf_time_noneE2 le_less_trans not_le to_trans_raw_sig_def zero_option_def) 
              finally have "False"
                using \<open>(\<tau>'(t' := 0)) x B \<noteq> None\<close> by blast }
            thus "\<And>x. x \<in> dom (to_trans_raw_sig (\<tau>'(t' := 0)) B) \<Longrightarrow> time < x"
              using le_less_linear by blast
          qed
          thus ?thesis
            using get_state_b_simulate_fin_inf_none[OF bigstep2_pre `B \<notin> set (signals_from nand4)`] 
            by auto
        qed
        finally have "signal_of (def B) \<tau> B i = get_state res' B"
          by auto
        have "time , get_state res' , get_event res' , get_beh res', def  \<turnstile> <Bassign_trans C (Bnand (Bsig A) (Bsig B)) 0 , get_trans res'> \<longrightarrow>\<^sub>s \<tau>_res"
          using conc_cases(1)[OF `time, get_state res', get_event res', get_beh res', def \<turnstile> <nand4, get_trans res'> \<longrightarrow>\<^sub>c \<tau>_res`[unfolded nand4_def]]
          `\<not> disjnt {A, B} (get_event res')` by auto
        obtain x' where " time , get_state res' , get_beh' res' , get_beh res', def  \<turnstile> Bnand (Bsig A) (Bsig B) \<longrightarrow>\<^sub>b x'" and 
          \<tau>_res_def: " trans_post_raw C x' (get_state res' C) (get_trans res') time 0 = \<tau>_res"
          using seq_cases_trans[OF `time , get_state res' , get_event res' , get_beh res', def  \<turnstile> <Bassign_trans C (Bnand (Bsig A) (Bsig B)) 0 , get_trans res'> \<longrightarrow>\<^sub>s \<tau>_res`]
          by blast
        have "time , get_state res' , get_beh' res' , get_beh res', def  \<turnstile> Bsig A \<longrightarrow>\<^sub>b Bv (bval_of (get_state res' A))"
          by (smt \<open>0 , def , {} , 0, def \<turnstile> Bnand (Bsig A) (Bsig B) \<longrightarrow>\<^sub>b x\<close> \<open>signal_of (def A) \<tau> A i =
          get_state res' A\<close> \<open>x = Bv (\<not> (bval_of (def A) \<and> bval_of (def B)))\<close> assms(4) assms(6)
          beval_cases(1) beval_cases(9) beval_raw.intros(1) signal_of_preserve_well_typedness
          styping_def ty.simps(3) type_of.simps(1) type_of.simps(2) val.exhaust_sel)
        moreover have "time , get_state res' , get_beh' res' , get_beh res', def  \<turnstile> Bsig B \<longrightarrow>\<^sub>b Bv (bval_of (get_state res' B))"
          by (smt \<open>time , get_state res' , get_beh' res' , get_beh res', def \<turnstile> Bnand (Bsig A) (Bsig B)
          \<longrightarrow>\<^sub>b x'\<close> \<open>time , get_state res' , get_beh' res' , get_beh res', def \<turnstile> Bsig A \<longrightarrow>\<^sub>b Bv (bval_of
          (get_state res' A))\<close> beval_cases(9) beval_raw.intros(1) beval_raw_deterministic
          val.distinct(1) val.exhaust_sel)
        ultimately have "x' = Bv (\<not> (bval_of (get_state res' A) \<and> bval_of (get_state res' B)))"
          using beval_cases(9)[OF `time , get_state res' , get_beh' res' , get_beh res', def  \<turnstile> Bnand (Bsig A) (Bsig B) \<longrightarrow>\<^sub>b x'`]
          by (smt beval_cases(1) val.distinct(1))
        have "\<not> post_necessary_raw 0 (get_trans res') time C x' (get_state res' C)"
        proof (rule ccontr)
          assume "\<not> \<not> post_necessary_raw 0 (get_trans res') time C x' (get_state res' C)"
          hence "post_necessary_raw 0 (get_trans res') time C x' (get_state res' C)"
            by auto
          hence "\<tau>_res time C = post_raw C x' (get_trans res') (time + 0) time C"
            unfolding \<tau>_res_def[THEN sym] trans_post_raw_def by auto
          hence "next_time time \<tau>_res = time"
            by (metis (no_types, lifting) \<open> next_time time \<tau>_res = Suc i\<close> \<open>time < Suc i\<close>
            add.right_neutral dual_order.strict_trans fun_upd_same next_time_at_least2
            option.distinct(1) post_raw_def zero_fun_def zero_option_def)
          thus "False"
            using `next_time time \<tau>_res = Suc i`  using \<open>time < Suc i\<close> by linarith
        qed
        moreover have "\<not> (\<exists>i\<le>time + 0 - 1. get_trans res' i C = Some x')"
          using b_simulate_fin_preserve_trans_removal[OF bigstep2_pre trans_removal] 
          by (metis (no_types, hide_lams) Suc_diff_1 \<open>t' < time \<or> t' = time\<close> add.right_neutral
          b_simulate_fin.intros(4) b_simulate_fin_deterministic bigstep2_pre comp_eq_dest_lhs
          diff_le_self fun_upd_same le_imp_less_Suc not_gr_zero not_le not_less_zero
          option.distinct(1) snd_conv zero_fun_def zero_option_def)
        ultimately have "x' = get_state res' C"
          unfolding post_necessary_raw_correctness by blast
        hence "bval_of (get_state res' C) \<longleftrightarrow> \<not> (bval_of (get_state res' A) \<and> bval_of (get_state res' B))"
          using `x' = Bv (\<not> (bval_of (get_state res' A) \<and> bval_of (get_state res' B)))`
          using val.sel(1) by presburger
        hence ?thesis
          using `signal_of (def A) \<tau> A i = get_state res' A` `signal_of (def B) \<tau> B i = get_state res' B`
          `signal_of (def C) (get_beh res) C i = get_state res' C` by auto }
        moreover
        { assume "next_time time \<tau>_res < Suc i"
          hence bigstep3: "Suc i, next_time time \<tau>_res , next_state time \<tau>_res (get_state res') , next_event time \<tau>_res (get_state res') , Femto_VHDL_raw.add_to_beh2 (get_state res') (get_beh res') time def, def \<turnstile> <nand4 , \<tau>_res (next_time time \<tau>_res := 0)> \<leadsto> res"
            using bau[OF bigstep2] 
            by (smt \<open>\<not> quiet (get_trans res') (get_beh' res')\<close> \<open>time , get_state res' , get_beh' res' , get_beh res', def \<turnstile> <nand4 , get_trans res'> \<longrightarrow>\<^sub>c \<tau>_res\<close> \<open>time < Suc i\<close> bigstep2 case_bau nat_less_le)
          have "\<tau>_res = 0 \<or> \<tau>_res \<noteq> 0"
            by auto
          moreover
          { assume "\<tau>_res = 0"
            hence "next_event time \<tau>_res (get_state res') = {}"
            proof -
              have "next_state time \<tau>_res (get_state res') = get_state res'"
                using `\<tau>_res = 0` unfolding next_state_def Let_def  by (simp add: zero_fun_def zero_option_def)
              thus ?thesis
                unfolding next_event_alt_def  by auto
            qed
            hence "quiet (\<tau>_res (next_time time \<tau>_res := 0)) (next_event time \<tau>_res (get_state res'))"
              using `\<tau>_res = 0`  by (simp add: fun_upd_idem_iff quiet_def zero_fun_def)
            hence "res = (Suc i, next_state time \<tau>_res (get_state res'), next_event time \<tau>_res (get_state res'), Femto_VHDL_raw.add_to_beh2 (get_state res') (get_beh res') time def, 0)"
              using bau[OF bigstep3] `next_time time \<tau>_res < Suc i` by auto
            hence gb_res: "get_beh res = Femto_VHDL_raw.add_to_beh2 (get_state res') (get_beh res') time def"
              by auto
            have "time \<le> i"
              using \<open>time < Suc i\<close> less_Suc_eq_le by blast
            have "\<forall>n>time. get_beh res' n C = 0"
              by (metis b_simulate_fin_preserves_hist bigstep2_pre trans_removal zero_fun_def)
            hence "signal_of (def C) (get_beh res) C i = get_state res' C"
              using signal_of_add_to_beh2'[OF `time \<le> i` ] unfolding gb_res by auto
            have "signal_of (def A) \<tau> A i  = signal_of (def A) \<tau>' A i"
              using init'_modifies_local_strongest[OF `init' 0 def {} 0 def nand4 \<tau> \<tau>'` `A \<notin> set (signals_from nand4)`]
              using \<open>trans_post_raw C x (def C) \<tau> 0 0 = \<tau>'\<close> signal_of_trans_post by fastforce
            also have "... = signal_of (\<sigma>' A) \<tau>' A i"
              by (metis \<open>inf_time (to_trans_raw_sig \<tau>) A i = Some time\<close> \<open>trans_post_raw C x (def C) \<tau> 0 0 = \<tau>'\<close> comp_apply option.simps(5) sig.distinct(3) signal_of_trans_post to_signal_def)
            also have "... = signal_of (\<sigma>' A) (\<tau>'(t':=0)) A i"
              by (smt \<open>next_state 0 \<tau>' def = \<sigma>'\<close> \<open>next_time 0 \<tau>' = t'\<close> comp_apply next_state_def next_time_at_least2 override_on_apply_in signal_of_rem_curr_trans_at_t)
            also have "... = signal_of (get_state res' A) (get_trans res') A i"
              using bau_signal_of[OF bigstep2_pre `A \<notin> set (signals_from nand4)` `time \<le> i` trans_removal]
              by blast
            also have "... = get_state res' A"
              by (metis (no_types, hide_lams) \<open>A \<notin> set (signals_from nand4)\<close> \<open>\<tau>_res = 0\<close> \<open>time , get_state res' , get_beh' res' , get_beh res', def \<turnstile> <nand4 , get_trans res'> \<longrightarrow>\<^sub>c \<tau>_res\<close> b_conc_exec_modifies_local_strongest signal_of_def zero_fun_def)
            finally have "signal_of (def A) \<tau> A i = get_state res' A"
              by auto
            have "signal_of (def B) \<tau> B i  = def B"
              using `inf_time (to_trans_raw_sig \<tau>) B i = None` 
              by (simp add: to_signal_def)
            also have "... = \<sigma>' B"
            proof -
              have "B \<notin> (dom (\<tau>' (next_time 0 \<tau>')))"
                using \<open>inf_time (to_trans_raw_sig \<tau>) B i = None\<close>
                using init'_modifies_local_strongest[OF `init' 0 def {} 0 def nand4 \<tau> \<tau>'` `B \<notin> set (signals_from nand4)`]          
                by (metis \<open>\<And>thesis. (\<And>time. \<lbrakk>inf_time (to_trans_raw_sig \<tau>) A i = Some time; inf_time
                (to_trans_raw_sig \<tau>) B i = None\<rbrakk> \<Longrightarrow> thesis) \<Longrightarrow> thesis\<close> \<open>next_time 0 \<tau>' = t'\<close> \<open>t' < time \<or> t'
                = time\<close> \<open>time \<le> i\<close> domIff dom_def inf_time_noneE2 not_le order.strict_trans
                to_trans_raw_sig_def zero_option_def)
              thus ?thesis
                unfolding `next_state 0 \<tau>' def = \<sigma>'`[THEN sym] next_state_def Let_def  by simp
            qed
            also have "... = get_state res' B"
            proof -
              have "inf_time (to_trans_raw_sig (\<tau>'(t' := 0))) B time = None"
                unfolding inf_time_none_iff[THEN sym]
              proof 
                { fix x 
                  assume " x \<in> dom (to_trans_raw_sig (\<tau>'(t' := 0)) B)"
                  hence "(\<tau>'(t' := 0)) x B \<noteq> None"
                    unfolding dom_def to_trans_raw_sig_def by auto
                  hence "x \<noteq> t'"
                    unfolding fun_upd_def zero_fun_def zero_option_def by auto
                  assume "x \<le> time"
                  have "(\<tau>'(t' := 0)) x B = \<tau>' x B"
                    using `x \<noteq> t'` by auto
                  also have "... = \<tau> x B"
                    using init'_modifies_local_strongest[OF `init' 0 def {} 0 def nand4 \<tau> \<tau>'` `B \<notin> set (signals_from nand4)`]          
                    by auto
                  also have "... = None"
                    using \<open>inf_time (to_trans_raw_sig \<tau>) B i = None\<close> \<open>time \<le> i\<close> 
                    by (metis \<open>x \<le> time\<close> inf_time_noneE2 le_less_trans not_le to_trans_raw_sig_def zero_option_def) 
                  finally have "False"
                    using \<open>(\<tau>'(t' := 0)) x B \<noteq> None\<close> by blast }
                thus "\<And>x. x \<in> dom (to_trans_raw_sig (\<tau>'(t' := 0)) B) \<Longrightarrow> time < x"
                  using le_less_linear by blast
              qed
              thus ?thesis
                using get_state_b_simulate_fin_inf_none[OF bigstep2_pre `B \<notin> set (signals_from nand4)`] 
                by auto
            qed
            finally have "signal_of (def B) \<tau> B i = get_state res' B"
              by auto
            have "time , get_state res' , get_event res' , get_beh res', def  \<turnstile> <Bassign_trans C (Bnand (Bsig A) (Bsig B)) 0 , get_trans res'> \<longrightarrow>\<^sub>s \<tau>_res"
              using conc_cases(1)[OF `time, get_state res', get_event res', get_beh res', def \<turnstile> <nand4, get_trans res'> \<longrightarrow>\<^sub>c \<tau>_res`[unfolded nand4_def]]
              `\<not> disjnt {A, B} (get_event res')` by auto
            obtain x' where " time , get_state res' , get_beh' res' , get_beh res', def  \<turnstile> Bnand (Bsig A) (Bsig B) \<longrightarrow>\<^sub>b x'" and 
              \<tau>_res_def: " trans_post_raw C x' (get_state res' C) (get_trans res') time 0 = \<tau>_res"
              using seq_cases_trans[OF `time , get_state res' , get_event res' , get_beh res', def  \<turnstile> <Bassign_trans C (Bnand (Bsig A) (Bsig B)) 0 , get_trans res'> \<longrightarrow>\<^sub>s \<tau>_res`]
              by blast
            have "time , get_state res' , get_beh' res' , get_beh res', def  \<turnstile> Bsig A \<longrightarrow>\<^sub>b Bv (bval_of (get_state res' A))"
              by (smt \<open>0 , def , {} , 0, def \<turnstile> Bnand (Bsig A) (Bsig B) \<longrightarrow>\<^sub>b x\<close> \<open>signal_of (def A) \<tau> A i =
              get_state res' A\<close> \<open>x = Bv (\<not> (bval_of (def A) \<and> bval_of (def B)))\<close> assms(4) assms(6)
              beval_cases(1) beval_cases(9) beval_raw.intros(1) signal_of_preserve_well_typedness
              styping_def ty.simps(3) type_of.simps(1) type_of.simps(2) val.exhaust_sel)
            moreover have "time , get_state res' , get_beh' res' , get_beh res', def  \<turnstile> Bsig B \<longrightarrow>\<^sub>b Bv (bval_of (get_state res' B))"
              by (smt \<open>time , get_state res' , get_beh' res' , get_beh res', def \<turnstile> Bnand (Bsig A) (Bsig B)
              \<longrightarrow>\<^sub>b x'\<close> \<open>time , get_state res' , get_beh' res' , get_beh res', def \<turnstile> Bsig A \<longrightarrow>\<^sub>b Bv (bval_of
              (get_state res' A))\<close> beval_cases(9) beval_raw.intros(1) beval_raw_deterministic
              val.distinct(1) val.exhaust_sel)
            ultimately have "x' = Bv (\<not> (bval_of (get_state res' A) \<and> bval_of (get_state res' B)))"
              using beval_cases(9)[OF `time , get_state res' , get_beh' res' , get_beh res', def  \<turnstile> Bnand (Bsig A) (Bsig B) \<longrightarrow>\<^sub>b x'`]
              by (smt beval_cases(1) val.distinct(1))
            have "\<not> post_necessary_raw 0 (get_trans res') time C x' (get_state res' C)"
            proof (rule ccontr)
              assume "\<not> \<not> post_necessary_raw 0 (get_trans res') time C x' (get_state res' C)"
              hence "post_necessary_raw 0 (get_trans res') time C x' (get_state res' C)"
                by auto
              hence "\<tau>_res time C = post_raw C x' (get_trans res') (time + 0) time C"
                unfolding \<tau>_res_def[THEN sym] trans_post_raw_def by auto
              hence "next_time time \<tau>_res = time"
                by (simp add: \<open>\<tau>_res = 0\<close> post_raw_def zero_fun_def zero_option_def)
              thus "False"
                using `next_time time \<tau>_res < Suc i`  using \<open>time < Suc i\<close> 
                by (simp add: \<open>\<tau>_res = 0\<close>)
            qed
            moreover have "\<not> (\<exists>i\<le>time + 0 - 1. get_trans res' i C = Some x')"
              using b_simulate_fin_preserve_trans_removal[OF bigstep2_pre trans_removal] 
              by (metis (no_types, hide_lams) Suc_diff_1 \<open>t' < time \<or> t' = time\<close> add.right_neutral
              b_simulate_fin.intros(4) b_simulate_fin_deterministic bigstep2_pre comp_eq_dest_lhs
              diff_le_self fun_upd_same le_imp_less_Suc not_gr_zero not_le not_less_zero
              option.distinct(1) snd_conv zero_fun_def zero_option_def)
            ultimately have "x' = get_state res' C"
              unfolding post_necessary_raw_correctness by blast
            hence "bval_of (get_state res' C) \<longleftrightarrow> \<not> (bval_of (get_state res' A) \<and> bval_of (get_state res' B))"
              using `x' = Bv (\<not> (bval_of (get_state res' A) \<and> bval_of (get_state res' B)))`
              using val.sel(1) by presburger
            hence ?thesis
              using `signal_of (def A) \<tau> A i = get_state res' A` `signal_of (def B) \<tau> B i = get_state res' B`
              `signal_of (def C) (get_beh res) C i = get_state res' C` by auto }
          moreover
          { assume "\<tau>_res \<noteq> 0"
            have "time , get_state res' , get_event res' , get_beh res', def  \<turnstile> <Bassign_trans C (Bnand (Bsig A) (Bsig B)) 0 , get_trans res'> \<longrightarrow>\<^sub>s \<tau>_res"
              using conc_cases(1)[OF `time, get_state res', get_event res', get_beh res', def \<turnstile> <nand4, get_trans res'> \<longrightarrow>\<^sub>c \<tau>_res`[unfolded nand4_def]]
              `\<not> disjnt {A, B} (get_event res')` by auto
            obtain x' where " time , get_state res' , get_beh' res' , get_beh res', def  \<turnstile> Bnand (Bsig A) (Bsig B) \<longrightarrow>\<^sub>b x'" and 
              \<tau>_res_def: " trans_post_raw C x' (get_state res' C) (get_trans res') time 0 = \<tau>_res"
              using seq_cases_trans[OF `time , get_state res' , get_event res' , get_beh res', def  \<turnstile> <Bassign_trans C (Bnand (Bsig A) (Bsig B)) 0 , get_trans res'> \<longrightarrow>\<^sub>s \<tau>_res`]
              by blast
            have "\<And>n. n < time \<Longrightarrow> \<tau>_res n = 0"
              using b_conc_exec_preserve_trans_removal[OF `time, get_state res', get_event res', get_beh res', def \<turnstile> <nand4, get_trans res'> \<longrightarrow>\<^sub>c \<tau>_res`]
              b_simulate_fin_preserve_trans_removal[OF bigstep2_pre trans_removal] by auto
            have "next_time time \<tau>_res = time"
            proof (rule ccontr)
              assume "next_time time \<tau>_res \<noteq> time" 
              hence "time < next_time time \<tau>_res"
                by (metis \<open>\<And>n. n < time \<Longrightarrow> \<tau>_res n = 0\<close> nat_less_le next_time_at_least)
              hence "\<tau>_res (next_time time \<tau>_res) C = None"
                unfolding \<tau>_res_def[THEN sym] trans_post_raw_def preempt_raw_def post_raw_def
                by (smt add.right_neutral dual_order.strict_implies_order fun_upd_eqD fun_upd_triv nat_neq_iff)
              have "next_time time \<tau>_res = (LEAST n. dom (\<tau>_res n) \<noteq> {})"
                using `\<tau>_res \<noteq> 0` unfolding next_time_def by auto
              hence "\<tau>_res time = 0"
                using `time < next_time time \<tau>_res`  using next_time_at_least2 by blast
              have "\<exists>n. dom (\<tau>_res n) \<noteq> {}"
                using `\<tau>_res \<noteq> 0` unfolding dom_def zero_fun_def zero_option_def by fastforce
              have "\<tau>_res (next_time time \<tau>_res) \<noteq> 0"
                by (metis (mono_tags, lifting) LeastI \<open>\<exists>n. dom (\<tau>_res n) \<noteq> {}\<close> \<open>next_time time \<tau>_res = (LEAST n. dom (\<tau>_res n) \<noteq> {})\<close> dom_eq_empty_conv zero_map)
              hence "\<tau>_res (next_time time \<tau>_res) A \<noteq> None \<or> \<tau>_res (next_time time \<tau>_res) B \<noteq> None "
                using `\<tau>_res (next_time time \<tau>_res) C = None` unfolding zero_fun_def zero_option_def 
                by (metis sig.exhaust)
              hence "get_trans res' (next_time time \<tau>_res) A \<noteq> None \<or> get_trans res' (next_time time \<tau>_res) B \<noteq> None"
                using b_conc_exec_modifies_local_strongest[OF `time, get_state res', get_event res', get_beh res', def \<turnstile> <nand4, get_trans res'> \<longrightarrow>\<^sub>c \<tau>_res`]
                by (simp add: \<open>A \<notin> set (signals_from nand4)\<close> \<open>B \<notin> set (signals_from nand4)\<close>)
              hence "(\<tau>'(t' := 0)) (next_time time \<tau>_res) A \<noteq> None \<or> (\<tau>'(t' := 0)) (next_time time \<tau>_res) B \<noteq> None"
                using b_simulate_fin_get_trans_gt_maxtime[OF bigstep2_pre `A \<notin> set (signals_from nand4)`]
                using b_simulate_fin_get_trans_gt_maxtime[OF bigstep2_pre `B \<notin> set (signals_from nand4)`]
                by (simp add: \<open>time < next_time time \<tau>_res\<close>)
              hence "\<tau>' (next_time time \<tau>_res) A \<noteq> None \<or> \<tau>' (next_time time \<tau>_res) B \<noteq> None"
                by (metis \<open>\<And>n. n < time \<Longrightarrow> \<tau>_res n = 0\<close> \<open>\<tau>_res (next_time time \<tau>_res) \<noteq> 0\<close> \<open>next_time time \<tau>_res \<noteq> time\<close> \<open>t' < time \<or> t' = time\<close> fun_upd_other)
              hence "\<tau> (next_time time \<tau>_res) A \<noteq> None \<or> \<tau> (next_time time \<tau>_res) B \<noteq> None"
                by (metis \<open>\<And>thesis. (\<And>x. \<lbrakk>0 , def , {} , 0, def \<turnstile> Bnand (Bsig A) (Bsig B) \<longrightarrow>\<^sub>b x;
                trans_post_raw C x (def C) \<tau> 0 0 = \<tau>'\<rbrakk> \<Longrightarrow> thesis) \<Longrightarrow> thesis\<close> sig.distinct(3)
                sig.distinct(5) to_trans_raw_sig_def trans_post_raw_diff_sig)
              thus "False"
                using inf_time_someE[OF \<open>inf_time (to_trans_raw_sig \<tau>) A i = Some time\<close>]
                \<open>time < next_time time \<tau>_res\<close> \<open>next_time time \<tau>_res < Suc i\<close>
                by (metis \<open>inf_time (to_trans_raw_sig \<tau>) B i = None\<close> domIff inf_time_noneE2 less_Suc_eq_le not_le to_trans_raw_sig_def zero_option_def)
            qed
            hence "\<tau>_res time \<noteq> 0"
              using `\<tau>_res \<noteq> 0` unfolding zero_fun_def zero_option_def next_time_def 
              by (metis (mono_tags, lifting) LeastI_ex dom_eq_empty_conv)
            have " get_trans res' time = 0"
              using get_trans_res_maxtime[OF bigstep2_pre ] by auto          
            hence "\<tau>_res time A = 0" and "\<tau>_res time B = 0"
              using b_conc_exec_modifies_local_strongest[OF `time, get_state res', get_event res', get_beh res', def \<turnstile> <nand4, get_trans res'> \<longrightarrow>\<^sub>c \<tau>_res` `A \<notin> set (signals_from nand4)`]
              using b_conc_exec_modifies_local_strongest[OF `time, get_state res', get_event res', get_beh res', def \<turnstile> <nand4, get_trans res'> \<longrightarrow>\<^sub>c \<tau>_res` `B \<notin> set (signals_from nand4)`]
              by (metis zero_fun_def)+
            hence " A \<notin> next_event time \<tau>_res (get_state res')" and " B \<notin> next_event time \<tau>_res (get_state res')"
              unfolding next_event_alt_def next_state_def \<open>next_time time \<tau>_res = time\<close> 
              by (smt domIff mem_Collect_eq override_on_def zero_option_def)+
            hence "disjnt {A, B} (next_event time \<tau>_res (get_state res'))"
              by auto
            have "\<tau>_res time C \<noteq> 0"
            proof (rule ccontr)
              assume "\<not> \<tau>_res time C \<noteq> 0" hence "\<tau>_res time C = 0" by auto
              hence "\<tau>_res time = 0"
                using `\<tau>_res time A = 0` `\<tau>_res time B = 0` 
                unfolding zero_fun_def zero_option_def  by (metis sig.exhaust)
              with `\<tau>_res time \<noteq> 0` show False 
                by auto
            qed
            have "post_necessary_raw 0 (get_trans res') time C x' (get_state res' C)"
            proof (rule ccontr)
              assume "\<not> post_necessary_raw 0 (get_trans res') time C x' (get_state res' C)"
              hence "\<tau>_res time C = 0"
                unfolding \<tau>_res_def[THEN sym] trans_post_raw_def preempt_raw_def by (auto simp add: zero_option_def)
              with `\<tau>_res time C \<noteq> 0` show False
                by auto
            qed
            hence "\<tau>_res time C = Some x'"
              unfolding \<tau>_res_def[THEN sym] trans_post_raw_def post_raw_def by auto
            have "\<not> (\<exists>i\<le>time + 0 - 1. get_trans res' i C = Some x')"
              using b_simulate_fin_preserve_trans_removal[OF bigstep2_pre trans_removal] 
              by (metis (no_types, hide_lams) Suc_diff_1 \<open>t' < time \<or> t' = time\<close> add.right_neutral
              b_simulate_fin.intros(4) b_simulate_fin_deterministic bigstep2_pre comp_eq_dest_lhs
              diff_le_self fun_upd_same le_imp_less_Suc not_gr_zero not_le not_less_zero
              option.distinct(1) snd_conv zero_fun_def zero_option_def)
            hence "get_state res' C \<noteq> x'"
              using `post_necessary_raw 0 (get_trans res') time C x' (get_state res' C)`
              unfolding post_necessary_raw_correctness2 
              by (metis (no_types, lifting) Suc_diff_1 \<open>next_time time \<tau>_res = time\<close> \<open>post_necessary_raw
              0 (get_trans res') time C x' (get_state res' C)\<close> \<tau>_res_def add.right_neutral
              le_imp_less_Suc next_time_at_least2 option.distinct(1) order.asym post_raw_def
              trans_post_raw_def zero_fun_def zero_option_def)
            hence "get_state res'  C \<noteq> the (\<tau>_res time C)"
              by (simp add: \<open>\<tau>_res time C = Some x'\<close>)
            hence "C \<in> (next_event time \<tau>_res (get_state res'))" 
              unfolding next_event_alt_def next_state_def 
              by (smt \<open>\<tau>_res time C \<noteq> 0\<close> \<open>next_time time \<tau>_res = time\<close> comp_def domIff mem_Collect_eq override_on_apply_in zero_option_def)
            hence "next_time time
                \<tau>_res , next_state time \<tau>_res
                         (get_state res') , next_event time \<tau>_res (get_state res') , Femto_VHDL_raw.add_to_beh2 (get_state res') (get_beh res') time def, def  \<turnstile> <nand4 , \<tau>_res
               (next_time time \<tau>_res := 0)> \<longrightarrow>\<^sub>c  \<tau>_res (next_time time \<tau>_res := 0)"
              using `disjnt {A, B} (next_event time \<tau>_res (get_state res'))` 
              unfolding nand4_def by (intro b_conc_exec.intros(1))
            have " \<not> quiet (\<tau>_res(next_time time \<tau>_res := 0)) (next_event time \<tau>_res (get_state res'))"
              by (metis \<open>C \<in> next_event time \<tau>_res (get_state res')\<close> empty_iff quiet_def)
    
            have "(\<tau>_res (next_time time \<tau>_res := 0)) \<noteq> 0 \<Longrightarrow> Suc i \<le> next_time (next_time time \<tau>_res) (\<tau>_res (next_time time \<tau>_res := 0))"
              unfolding `next_time time \<tau>_res = time`
            proof (rule ccontr)
              assume " \<tau>_res(time := 0) \<noteq> 0"
              assume "\<not> Suc i \<le> next_time time (\<tau>_res (time := 0))"
              hence "next_time time (\<tau>_res (time := 0)) < Suc i"
                by auto
              have "to_trans_raw_sig (\<tau>_res (time := 0)) C = 0"
                using `\<And>n. n < time \<Longrightarrow> \<tau>_res n = 0`
                using `post_necessary_raw 0 (get_trans res') time C x' (get_state res' C)`
                unfolding to_trans_raw_sig_def \<tau>_res_def[THEN sym] trans_post_raw_def post_raw_def
                zero_fun_def zero_option_def 
                by (intro ext) auto
              have tr: "\<And>n. n < time \<Longrightarrow> (\<tau>_res (time := 0)) n = 0"
                using `\<And>n. n < time \<Longrightarrow> \<tau>_res n = 0` by auto
              have "time \<le> next_time time (\<tau>_res (time := 0))"
                by (intro next_time_at_least[OF tr] )
              moreover have "time \<noteq> next_time time (\<tau>_res (time := 0))"
                by (smt Suc_eq_plus1 Suc_n_not_le_n fun_upd_same less_Suc_eq next_time_at_least next_time_def tr)
              ultimately have "time < next_time time (\<tau>_res (time := 0))"
                by auto
              have "(\<tau>_res(time := 0)) (next_time time (\<tau>_res (time := 0))) \<noteq> 0"
                using `\<tau>_res (time := 0) \<noteq> 0` unfolding next_time_def zero_fun_def zero_option_def
              proof -
                assume a1: "\<tau>_res(time := Map.empty) \<noteq> (\<lambda>x. Map.empty)"
                have f2: "\<And>n. {s. (\<tau>_res(time := Map.empty)) n s \<noteq> None} = {} \<or> dom ((\<tau>_res(time := Map.empty)) (LEAST n. dom ((\<tau>_res(time := Map.empty)) n) \<noteq> {})) \<noteq> {}"
                  by (metis (mono_tags, lifting) LeastI_ex a1 dom_eq_empty_conv) 
                obtain nn :: nat and ss :: sig where f3: "(\<tau>_res(time := Map.empty)) nn ss \<noteq> None"
                  using a1 by meson
                obtain ssa :: "(sig \<Rightarrow> val option) \<Rightarrow> sig" where f4: "\<And>f s fa. (dom f \<noteq> {} \<or> f (s::sig) = (None::val option)) \<and> (fa (ssa fa) \<noteq> None \<or> dom fa = {})"
                  by (metis (no_types) dom_eq_empty_conv)
                then have "{s. (\<tau>_res(time := Map.empty)) (LEAST n. dom ((\<tau>_res(time := Map.empty)) n) \<noteq> {}) s \<noteq> None} \<noteq> {}"
                  using f3 f2 by (metis (no_types) dom_def)
                then have "{s. (\<tau>_res(time := Map.empty)) (if \<forall>n s. (\<tau>_res(time := Map.empty)) n s = None then Suc time else LEAST n. dom ((\<tau>_res(time := Map.empty)) n) \<noteq> {}) s \<noteq> None} = {} \<longrightarrow> (\<forall>n s. (\<tau>_res(time := Map.empty)) n s = None)"
                  by presburger
                then have "\<exists>s. (\<tau>_res(time := Map.empty)) (if \<forall>n s. (\<tau>_res(time := Map.empty)) n s = None then Suc time else LEAST n. dom ((\<tau>_res(time := Map.empty)) n) \<noteq> {}) s \<noteq> None"
                  using f4 f3 by blast
                then show "(\<tau>_res(time := Map.empty)) (if \<tau>_res(time := Map.empty) = (\<lambda>n. Map.empty) then time + 1 else LEAST n. dom ((\<tau>_res(time := Map.empty)) n) \<noteq> {}) \<noteq> Map.empty"
                  by (metis Suc_eq_plus1)
              qed
              hence "(\<tau>_res(time := 0)) (next_time time (\<tau>_res (time := 0))) A \<noteq> 0 \<or> 
                    (\<tau>_res(time := 0)) (next_time time (\<tau>_res (time := 0))) B \<noteq> 0" 
                using `to_trans_raw_sig (\<tau>_res (time := 0)) C = 0` unfolding to_trans_raw_sig_def
              proof -
                assume a1: "(\<lambda>n. (\<tau>_res(time := 0)) n C) = 0"
                obtain ss :: "sig set \<Rightarrow> sig set \<Rightarrow> sig" where
                  "\<forall>x0 x1. (\<exists>v2. v2 \<in> x1 \<and> v2 \<notin> x0) = (ss x0 x1 \<in> x1 \<and> ss x0 x1 \<notin> x0)"
                  by moura
                then have f2: "\<forall>S Sa. ss Sa S \<in> S \<and> ss Sa S \<notin> Sa \<or> S \<subseteq> Sa"
                  by (meson subsetI)
                then have "dom (0::sig \<Rightarrow> val option) \<subseteq> {}"
                  by (meson domIff zero_map)
                then have f3: "\<not> dom ((\<tau>_res(time := 0)) (next_time time (\<tau>_res(time := 0)))) \<subseteq> {}"
                  using \<open>(\<tau>_res(time := 0)) (next_time time (\<tau>_res(time := 0))) \<noteq> 0\<close> by auto
                have "(\<tau>_res(time := 0)) (next_time time (\<tau>_res(time := 0))) C = None"
                  using a1 by (metis (no_types) zero_map)
                then show ?thesis
                  using f3 f2 by (metis (full_types) domIff sig.exhaust zero_option_def)
              qed
              hence "get_trans res' (next_time time (\<tau>_res (time := 0))) A \<noteq> 0 \<or> 
                     get_trans res' (next_time time (\<tau>_res (time := 0))) B \<noteq> 0"
                using b_conc_exec_modifies_local_strongest[OF `time, get_state res', get_event res', get_beh res', def \<turnstile> <nand4, get_trans res'> \<longrightarrow>\<^sub>c \<tau>_res` `A \<notin> set (signals_from nand4)`]
                using b_conc_exec_modifies_local_strongest[OF `time, get_state res', get_event res', get_beh res', def \<turnstile> <nand4, get_trans res'> \<longrightarrow>\<^sub>c \<tau>_res` `A \<notin> set (signals_from nand4)`]
                using `time < next_time time (\<tau>_res (time := 0))` 
                using \<open>B \<notin> set (signals_from nand4)\<close> \<open>time , get_state res' , get_beh' res' , get_beh res', def \<turnstile> <nand4 , get_trans res'> \<longrightarrow>\<^sub>c \<tau>_res\<close> b_conc_exec_modifies_local_strongest by fastforce
              hence "(\<tau>'(t' := 0)) (next_time time (\<tau>_res(time := 0))) A \<noteq> None \<or> (\<tau>'(t' := 0)) (next_time time (\<tau>_res(time := 0))) B \<noteq> None"
                using b_simulate_fin_get_trans_gt_maxtime[OF bigstep2_pre `A \<notin> set (signals_from nand4)`]
                using b_simulate_fin_get_trans_gt_maxtime[OF bigstep2_pre `B \<notin> set (signals_from nand4)`]
                by (simp add: \<open>time < next_time time (\<tau>_res(time := 0))\<close> zero_option_def)
              hence "\<tau>' (next_time time (\<tau>_res(time := 0))) A \<noteq> None \<or> \<tau>' (next_time time (\<tau>_res(time := 0))) B \<noteq> None"
                by (metis fun_upd_other fun_upd_same zero_map)
              hence "\<tau> (next_time time (\<tau>_res(time := 0))) A \<noteq> None \<or> \<tau> (next_time time (\<tau>_res(time := 0))) B \<noteq> None"
                by (metis \<open>\<And>thesis. (\<And>x. \<lbrakk>0 , def , {} , 0, def \<turnstile> Bnand (Bsig A) (Bsig B) \<longrightarrow>\<^sub>b x;
                trans_post_raw C x (def C) \<tau> 0 0 = \<tau>'\<rbrakk> \<Longrightarrow> thesis) \<Longrightarrow> thesis\<close> sig.distinct(3)
                sig.distinct(5) to_trans_raw_sig_def trans_post_raw_diff_sig)
              thus "False"
                using inf_time_someE[OF \<open>inf_time (to_trans_raw_sig \<tau>) A i = Some time\<close>]
                \<open>time < next_time time (\<tau>_res(time:= 0))\<close> \<open>next_time time (\<tau>_res(time := 0)) < Suc i\<close>
                by (metis Suc_leI \<open>inf_time (to_trans_raw_sig \<tau>) B i = None\<close> domIff inf_time_noneE2 not_less_eq_eq to_trans_raw_sig_def zero_option_def)
            qed
            have "(\<tau>_res (next_time time \<tau>_res := 0)) = 0 \<Longrightarrow> next_time (next_time time \<tau>_res) (\<tau>_res (next_time time \<tau>_res := 0)) \<le> Suc i"
              unfolding `next_time time \<tau>_res = time` using `time < Suc i` by auto
            have "(\<tau>_res (next_time time \<tau>_res := 0)) = 0 \<or> (\<tau>_res (next_time time \<tau>_res := 0)) \<noteq> 0"
              by auto
            moreover
            { assume "(\<tau>_res (next_time time \<tau>_res := 0)) = 0"
              hence " next_time (next_time time \<tau>_res) (\<tau>_res (next_time time \<tau>_res := 0)) \<le> Suc i"
                using \<open>\<tau>_res(next_time time \<tau>_res := 0) = 0 \<Longrightarrow> next_time (next_time time \<tau>_res) (\<tau>_res(next_time time \<tau>_res := 0)) \<le> Suc i\<close> by blast
              hence bigstep4: " Suc i, next_time (next_time time \<tau>_res) (\<tau>_res (next_time time \<tau>_res := 0)) , 
                                       next_state (next_time time \<tau>_res) (\<tau>_res (next_time time \<tau>_res := 0)) (next_state time \<tau>_res (get_state res')) , 
                                       next_event (next_time time \<tau>_res) (\<tau>_res (next_time time \<tau>_res := 0)) (next_state time \<tau>_res (get_state res')) , 
                                       Femto_VHDL_raw.add_to_beh2 (next_state time \<tau>_res (get_state res')) (Femto_VHDL_raw.add_to_beh2 (get_state res') (get_beh res') time def) (next_time time \<tau>_res) def, def \<turnstile> 
                                        <nand4 , (\<tau>_res (next_time time \<tau>_res := 0)) (next_time (next_time time \<tau>_res) (\<tau>_res (next_time time \<tau>_res := 0)) := 0)> \<leadsto> res"
                using bau[OF bigstep3] `next_time time \<tau>_res < Suc i` 
                by (smt \<open>C \<in> next_event time \<tau>_res (get_state res')\<close> \<open>next_time time \<tau>_res , next_state time \<tau>_res (get_state res') , next_event time \<tau>_res (get_state res') , Femto_VHDL_raw.add_to_beh2 (get_state res') (get_beh res') time def, def \<turnstile> <nand4 , \<tau>_res (next_time time \<tau>_res := 0)> \<longrightarrow>\<^sub>c \<tau>_res (next_time time \<tau>_res := 0)\<close> bigstep3 case_bau empty_iff quiet_def)
              have "next_event (next_time time \<tau>_res) (\<tau>_res (next_time time \<tau>_res := 0)) (next_state time \<tau>_res (get_state res')) = {}"
                unfolding `(\<tau>_res (next_time time \<tau>_res := 0)) = 0` next_event_alt_def  next_state_def
                Let_def zero_fun_def zero_option_def 
                by (smt \<open>\<tau>_res(next_time time \<tau>_res := 0) = 0\<close> domIff empty_Collect_eq fun_upd_apply override_on_apply_notin zero_fun_def zero_map)
              have " (\<tau>_res (next_time time \<tau>_res := 0)) (next_time (next_time time \<tau>_res) (\<tau>_res (next_time time \<tau>_res := 0)) := 0) = 0"
                using `(\<tau>_res (next_time time \<tau>_res := 0)) = 0`  by (simp add: fun_upd_idem_iff zero_fun_def)
              have "next_time (next_time time \<tau>_res) (\<tau>_res (next_time time \<tau>_res := 0)) < Suc i \<or> next_time (next_time time \<tau>_res) (\<tau>_res (next_time time \<tau>_res := 0)) = Suc i"
                using \<open>next_time (next_time time \<tau>_res) (\<tau>_res(next_time time \<tau>_res := 0)) \<le> Suc i\<close> le_imp_less_or_eq by blast
              moreover
              { assume "next_time (next_time time \<tau>_res) (\<tau>_res (next_time time \<tau>_res := 0)) = Suc i"
                hence "res =
         (Suc i, next_state (next_time time \<tau>_res) (\<tau>_res(next_time time \<tau>_res := 0)) (next_state time \<tau>_res (get_state res')),
          next_event (next_time time \<tau>_res) (\<tau>_res(next_time time \<tau>_res := 0)) (next_state time \<tau>_res (get_state res')),
          Femto_VHDL_raw.add_to_beh2 (next_state time \<tau>_res (get_state res'))
           (Femto_VHDL_raw.add_to_beh2 (get_state res') (get_beh res') time def) (next_time time \<tau>_res) def,
          \<tau>_res(next_time time \<tau>_res := 0, next_time (next_time time \<tau>_res) (\<tau>_res(next_time time \<tau>_res := 0)) := 0))"
                  using bau[OF bigstep4] by auto
                hence gb_res: "get_beh res = Femto_VHDL_raw.add_to_beh2 (next_state time \<tau>_res (get_state res')) (Femto_VHDL_raw.add_to_beh2 (get_state res') (get_beh res') time def) (next_time time \<tau>_res) def"
                  by auto }
              moreover
              { assume "next_time (next_time time \<tau>_res) (\<tau>_res (next_time time \<tau>_res := 0)) < Suc i"
                hence "res =
         (Suc i, next_state (next_time time \<tau>_res) (\<tau>_res(next_time time \<tau>_res := 0)) (next_state time \<tau>_res (get_state res')),
          next_event (next_time time \<tau>_res) (\<tau>_res(next_time time \<tau>_res := 0)) (next_state time \<tau>_res (get_state res')),
          Femto_VHDL_raw.add_to_beh2 (next_state time \<tau>_res (get_state res'))
           (Femto_VHDL_raw.add_to_beh2 (get_state res') (get_beh res') time def) (next_time time \<tau>_res) def,
          0)"
                  using bau[OF bigstep4] 
                  by (smt \<open>\<tau>_res (next_time time \<tau>_res := 0, next_time (next_time time \<tau>_res)
                  (\<tau>_res(next_time time \<tau>_res := 0)) := 0) = 0\<close> \<open>next_event (next_time time \<tau>_res)
                  (\<tau>_res(next_time time \<tau>_res := 0)) (next_state time \<tau>_res (get_state res')) = {}\<close>
                  quiet_def)
                hence "get_beh res = Femto_VHDL_raw.add_to_beh2 (next_state time \<tau>_res (get_state res'))
           (Femto_VHDL_raw.add_to_beh2 (get_state res') (get_beh res') time def) (next_time time \<tau>_res) def"
                  by auto }
              ultimately have gb_res: "get_beh res = Femto_VHDL_raw.add_to_beh2 (next_state time \<tau>_res (get_state res')) (Femto_VHDL_raw.add_to_beh2 (get_state res') (get_beh res') time def) (next_time time \<tau>_res) def"
                by auto
              have " (next_time time \<tau>_res) \<le> i"
                using \<open>next_time time \<tau>_res < Suc i\<close> less_Suc_eq_le by blast
              have "signal_of (def C) (get_beh res) C i = (next_state time \<tau>_res (get_state res')) C"
                unfolding gb_res
                apply (intro signal_of_add_to_beh2'[OF `next_time time \<tau>_res \<le> i`] )
                by (smt Femto_VHDL_raw.add_to_beh2_def \<open>next_time time \<tau>_res = time\<close> b_simulate_fin_preserves_hist bigstep2_pre fun_upd_other nat_neq_iff trans_removal zero_fun_def)
              also have "... = the (\<tau>_res time C)"
                unfolding next_state_def `next_time time \<tau>_res = time` Let_def 
                by (metis \<open>\<tau>_res time C \<noteq> 0\<close> comp_apply domIff override_on_apply_in zero_option_def)
              also have "... = x'"
                by (simp add: \<open>\<tau>_res time C = Some x'\<close>)
              finally have "signal_of (def C) (get_beh res) C i = x'"
                by auto
              have "signal_of (def A) \<tau> A i  = signal_of (def A) \<tau>' A i"
                using init'_modifies_local_strongest[OF `init' 0 def {} 0 def nand4 \<tau> \<tau>'` `A \<notin> set (signals_from nand4)`]
                using \<open>trans_post_raw C x (def C) \<tau> 0 0 = \<tau>'\<close> signal_of_trans_post by fastforce
              also have "... = signal_of (\<sigma>' A) \<tau>' A i"
                by (metis \<open>inf_time (to_trans_raw_sig \<tau>) A i = Some time\<close> \<open>trans_post_raw C x (def C) \<tau> 0 0 = \<tau>'\<close> comp_apply option.simps(5) sig.distinct(3) signal_of_trans_post to_signal_def)
              also have "... = signal_of (\<sigma>' A) (\<tau>'(t':=0)) A i"
                by (smt \<open>next_state 0 \<tau>' def = \<sigma>'\<close> \<open>next_time 0 \<tau>' = t'\<close> comp_apply next_state_def next_time_at_least2 override_on_apply_in signal_of_rem_curr_trans_at_t)
              also have "... = signal_of (get_state res' A) (get_trans res') A i"
                using bau_signal_of[OF bigstep2_pre `A \<notin> set (signals_from nand4)` _ trans_removal] `time < Suc i`
                using less_Suc_eq_le by blast
              also have "... = get_state res' A"
                by (metis (mono_tags, lifting) \<open>A \<notin> set (signals_from nand4)\<close> \<open>\<tau>_res time A = 0\<close>
                \<open>\<tau>_res(next_time time \<tau>_res := 0) = 0\<close> \<open>next_time time \<tau>_res = time\<close> \<open>time , get_state
                res' , get_beh' res' , get_beh res', def \<turnstile> <nand4 , get_trans res'> \<longrightarrow>\<^sub>c \<tau>_res\<close>
                b_conc_exec_modifies_local_strongest fun_upd_def signal_of_def zero_fun_def)
              finally have "signal_of (def A) \<tau> A i = get_state res' A"
                by auto
              have "signal_of (def B) \<tau> B i  = def B"
                using `inf_time (to_trans_raw_sig \<tau>) B i = None` 
                by (simp add: to_signal_def)
              also have "... = \<sigma>' B"
              proof -
                have "B \<notin> (dom (\<tau>' (next_time 0 \<tau>')))"
                  using \<open>inf_time (to_trans_raw_sig \<tau>) B i = None\<close>
                  using init'_modifies_local_strongest[OF `init' 0 def {} 0 def nand4 \<tau> \<tau>'` `B \<notin> set (signals_from nand4)`]          
                  by (metis \<open>next_time 0 \<tau>' \<le> time\<close> \<open>next_time time \<tau>_res = time\<close> \<open>next_time time \<tau>_res \<le> i\<close> domD domI inf_time_none_iff leD le_trans to_trans_raw_sig_def)
                thus ?thesis
                  unfolding `next_state 0 \<tau>' def = \<sigma>'`[THEN sym] next_state_def Let_def  by simp
              qed
              also have "... = get_state res' B"
              proof -
                have "inf_time (to_trans_raw_sig (\<tau>'(t' := 0))) B time = None"
                  unfolding inf_time_none_iff[THEN sym]
                proof 
                  { fix x 
                    assume " x \<in> dom (to_trans_raw_sig (\<tau>'(t' := 0)) B)"
                    hence "(\<tau>'(t' := 0)) x B \<noteq> None"
                      unfolding dom_def to_trans_raw_sig_def by auto
                    hence "x \<noteq> t'"
                      unfolding fun_upd_def zero_fun_def zero_option_def by auto
                    assume "x \<le> time"
                    have "(\<tau>'(t' := 0)) x B = \<tau>' x B"
                      using `x \<noteq> t'` by auto
                    also have "... = \<tau> x B"
                      using init'_modifies_local_strongest[OF `init' 0 def {} 0 def nand4 \<tau> \<tau>'` `B \<notin> set (signals_from nand4)`]          
                      by auto
                    also have "... = None"
                      using \<open>inf_time (to_trans_raw_sig \<tau>) B i = None\<close> 
                      by (metis \<open>inf_time (to_trans_raw_sig \<tau>) A i = Some time\<close> \<open>x \<le> time\<close> inf_time_at_most inf_time_noneE2 le_trans to_trans_raw_sig_def zero_option_def) 
                    finally have "False"
                      using \<open>(\<tau>'(t' := 0)) x B \<noteq> None\<close> by blast }
                  thus "\<And>x. x \<in> dom (to_trans_raw_sig (\<tau>'(t' := 0)) B) \<Longrightarrow> time < x"
                    using le_less_linear by blast
                qed
                thus ?thesis
                  using get_state_b_simulate_fin_inf_none[OF bigstep2_pre `B \<notin> set (signals_from nand4)`] 
                  by auto
              qed
              finally have "signal_of (def B) \<tau> B i = get_state res' B"
                by auto
              have "time , get_state res' , get_beh' res' , get_beh res', def  \<turnstile> Bsig A \<longrightarrow>\<^sub>b Bv (bval_of (get_state res' A))"
                by (smt \<open>0 , def , {} , 0, def \<turnstile> Bnand (Bsig A) (Bsig B) \<longrightarrow>\<^sub>b x\<close> \<open>signal_of (def A) \<tau> A i =
                get_state res' A\<close> \<open>x = Bv (\<not> (bval_of (def A) \<and> bval_of (def B)))\<close> assms(4) assms(6)
                beval_cases(1) beval_cases(9) beval_raw.intros(1) signal_of_preserve_well_typedness
                styping_def ty.simps(3) type_of.simps(1) type_of.simps(2) val.exhaust_sel)
              moreover have "time , get_state res' , get_beh' res' , get_beh res', def  \<turnstile> Bsig B \<longrightarrow>\<^sub>b Bv (bval_of (get_state res' B))"
                by (smt \<open>time , get_state res' , get_beh' res' , get_beh res', def \<turnstile> Bnand (Bsig A) (Bsig B)
                \<longrightarrow>\<^sub>b x'\<close> \<open>time , get_state res' , get_beh' res' , get_beh res', def \<turnstile> Bsig A \<longrightarrow>\<^sub>b Bv (bval_of
                (get_state res' A))\<close> beval_cases(9) beval_raw.intros(1) beval_raw_deterministic
                val.distinct(1) val.exhaust_sel)
              ultimately have "x' = Bv (\<not> (bval_of (get_state res' A) \<and> bval_of (get_state res' B)))"
                using beval_cases(9)[OF `time , get_state res' , get_beh' res' , get_beh res', def  \<turnstile> Bnand (Bsig A) (Bsig B) \<longrightarrow>\<^sub>b x'`]
                by (smt beval_cases(1) val.distinct(1))
              hence ?thesis
                using \<open>signal_of (def A) \<tau> A i = get_state res' A\<close> \<open>signal_of (def B) \<tau> B i = get_state res' B\<close> \<open>signal_of (def C) (get_beh res) C i = x'\<close> 
                by auto }
            moreover
            { assume " (\<tau>_res (next_time time \<tau>_res := 0)) \<noteq> 0"
              hence "Suc i \<le> next_time (next_time time \<tau>_res) (\<tau>_res (next_time time \<tau>_res := 0))"
                using \<open>\<tau>_res(next_time time \<tau>_res := 0) \<noteq> 0 \<Longrightarrow> Suc i \<le> next_time (next_time time \<tau>_res)
                (\<tau>_res(next_time time \<tau>_res := 0))\<close> by metis
              hence "Suc i < next_time (next_time time \<tau>_res) (\<tau>_res (next_time time \<tau>_res := 0)) \<or> Suc i = next_time (next_time time \<tau>_res) (\<tau>_res (next_time time \<tau>_res := 0))"        
                by auto
              moreover
              { assume "Suc i = next_time (next_time time \<tau>_res) (\<tau>_res (next_time time \<tau>_res := 0))"
                hence bigstep4: " Suc i, next_time (next_time time \<tau>_res) (\<tau>_res (next_time time \<tau>_res := 0)) , 
                                         next_state (next_time time \<tau>_res) (\<tau>_res (next_time time \<tau>_res := 0)) (next_state time \<tau>_res (get_state res')) , 
                                         next_event (next_time time \<tau>_res) (\<tau>_res (next_time time \<tau>_res := 0)) (next_state time \<tau>_res (get_state res')) , 
                                         Femto_VHDL_raw.add_to_beh2 (next_state time \<tau>_res (get_state res')) (Femto_VHDL_raw.add_to_beh2 (get_state res') (get_beh res') time def) (next_time time \<tau>_res) def, def \<turnstile> 
                                          <nand4 , (\<tau>_res (next_time time \<tau>_res := 0)) (next_time (next_time time \<tau>_res) (\<tau>_res (next_time time \<tau>_res := 0)) := 0)> \<leadsto> res"
                  using bau[OF bigstep3] `next_time time \<tau>_res < Suc i` 
                  by (smt \<open>Suc i \<le> next_time (next_time time \<tau>_res) (\<tau>_res(next_time time \<tau>_res := 0))\<close> \<open>\<tau>_res(next_time time \<tau>_res := 0) \<noteq> 0\<close> \<open>next_time time \<tau>_res , next_state time \<tau>_res (get_state res') , next_event time \<tau>_res (get_state res') , Femto_VHDL_raw.add_to_beh2 (get_state res') (get_beh res') time def, def \<turnstile> <nand4 , \<tau>_res (next_time time \<tau>_res := 0)> \<longrightarrow>\<^sub>c \<tau>_res (next_time time \<tau>_res := 0)\<close> bigstep3 case_bau quiet_def)
                hence "res =
         (Suc i, next_state (next_time time \<tau>_res) (\<tau>_res(next_time time \<tau>_res := 0)) (next_state time \<tau>_res (get_state res')),
          next_event (next_time time \<tau>_res) (\<tau>_res(next_time time \<tau>_res := 0)) (next_state time \<tau>_res (get_state res')),
          Femto_VHDL_raw.add_to_beh2 (next_state time \<tau>_res (get_state res'))
           (Femto_VHDL_raw.add_to_beh2 (get_state res') (get_beh res') time def) (next_time time \<tau>_res) def,
          \<tau>_res(next_time time \<tau>_res := 0, next_time (next_time time \<tau>_res) (\<tau>_res(next_time time \<tau>_res := 0)) := 0))"
                  using bau[OF bigstep4] 
                  using \<open>Suc i = next_time (next_time time \<tau>_res) (\<tau>_res(next_time time \<tau>_res := 0))\<close> by fastforce
                hence "get_beh res = Femto_VHDL_raw.add_to_beh2 (next_state time \<tau>_res (get_state res')) (Femto_VHDL_raw.add_to_beh2 (get_state res') (get_beh res') time def) (next_time time \<tau>_res) def"
                  by auto }
              moreover
              { assume "Suc i < next_time (next_time time \<tau>_res) (\<tau>_res (next_time time \<tau>_res := 0))"
                hence "res =
               (Suc i, next_state time \<tau>_res (get_state res'), {},
                Femto_VHDL_raw.add_to_beh2 (next_state time \<tau>_res (get_state res'))
                 (Femto_VHDL_raw.add_to_beh2 (get_state res') (get_beh res') time def) (next_time time \<tau>_res) def, \<tau>_res (next_time time \<tau>_res := 0))"
                  using bau[OF bigstep3] `next_time time \<tau>_res < Suc i` \<open> \<not> quiet (\<tau>_res(next_time time \<tau>_res := 0)) (next_event time \<tau>_res (get_state res'))\<close>
                  \<open>next_time time
                \<tau>_res , next_state time \<tau>_res
                         (get_state res') , next_event time \<tau>_res (get_state res') , Femto_VHDL_raw.add_to_beh2 (get_state res') (get_beh res') time def, def  \<turnstile> <nand4 , \<tau>_res
               (next_time time \<tau>_res := 0)> \<longrightarrow>\<^sub>c  \<tau>_res (next_time time \<tau>_res := 0)\<close> 
                  by (smt b_conc_exec_deterministic less_le_not_le)
                hence "get_beh res = Femto_VHDL_raw.add_to_beh2 (next_state time \<tau>_res (get_state res')) (Femto_VHDL_raw.add_to_beh2 (get_state res') (get_beh res') time def) (next_time time \<tau>_res) def"
                  by auto }
              ultimately have gb_res: "get_beh res = Femto_VHDL_raw.add_to_beh2 (next_state time \<tau>_res (get_state res')) (Femto_VHDL_raw.add_to_beh2 (get_state res') (get_beh res') time def) (next_time time \<tau>_res) def"
                  by auto
              have " (next_time time \<tau>_res) \<le> i"
                using \<open>next_time time \<tau>_res < Suc i\<close> less_Suc_eq_le by blast
              have "signal_of (def C) (get_beh res) C i = (next_state time \<tau>_res (get_state res')) C"
                unfolding gb_res
                apply (intro signal_of_add_to_beh2'[OF `next_time time \<tau>_res \<le> i`] )
                by (smt Femto_VHDL_raw.add_to_beh2_def \<open>next_time time \<tau>_res = time\<close> b_simulate_fin_preserves_hist bigstep2_pre fun_upd_other nat_neq_iff trans_removal zero_fun_def)
              also have "... = the (\<tau>_res time C)"
                unfolding next_state_def `next_time time \<tau>_res = time` Let_def 
                by (metis \<open>\<tau>_res time C \<noteq> 0\<close> comp_apply domIff override_on_apply_in zero_option_def)
              also have "... = x'"
                by (simp add: \<open>\<tau>_res time C = Some x'\<close>)
              finally have "signal_of (def C) (get_beh res) C i = x'"
                by auto
              have "signal_of (def A) \<tau> A i  = signal_of (def A) \<tau>' A i"
                using init'_modifies_local_strongest[OF `init' 0 def {} 0 def nand4 \<tau> \<tau>'` `A \<notin> set (signals_from nand4)`]
                using \<open>trans_post_raw C x (def C) \<tau> 0 0 = \<tau>'\<close> signal_of_trans_post by fastforce
              also have "... = signal_of (\<sigma>' A) \<tau>' A i"
                by (metis \<open>inf_time (to_trans_raw_sig \<tau>) A i = Some time\<close> \<open>trans_post_raw C x (def C) \<tau> 0 0 = \<tau>'\<close> comp_apply option.simps(5) sig.distinct(3) signal_of_trans_post to_signal_def)
              also have "... = signal_of (\<sigma>' A) (\<tau>'(t':=0)) A i"
                by (smt \<open>next_state 0 \<tau>' def = \<sigma>'\<close> \<open>next_time 0 \<tau>' = t'\<close> comp_apply next_state_def next_time_at_least2 override_on_apply_in signal_of_rem_curr_trans_at_t)
              also have "... = signal_of (get_state res' A) (get_trans res') A i"
                using bau_signal_of[OF bigstep2_pre `A \<notin> set (signals_from nand4)` _ trans_removal] `time < Suc i`
                using less_Suc_eq_le by blast
              also have "... = get_state res' A"
                by (smt \<open>A \<notin> set (signals_from nand4)\<close> \<open>Suc i \<le> next_time (next_time time \<tau>_res)
                (\<tau>_res(next_time time \<tau>_res := 0))\<close> \<open>\<tau>_res time A = 0\<close> \<open>get_trans res' time = 0\<close>
                \<open>next_time time \<tau>_res = time\<close> \<open>time , get_state res' , get_beh' res' , get_beh res', def
                \<turnstile> <nand4 , get_trans res'> \<longrightarrow>\<^sub>c \<tau>_res\<close> antisym_conv2 b_conc_exec_modifies_local_strongest
                dual_order.strict_trans2 fun_upd_other lessI next_time_at_least2 signal_of_def
                signal_of_suc_sig)
              finally have "signal_of (def A) \<tau> A i = get_state res' A"
                by auto
              have "signal_of (def B) \<tau> B i  = def B"
                using `inf_time (to_trans_raw_sig \<tau>) B i = None` 
                by (simp add: to_signal_def)
              also have "... = \<sigma>' B"
              proof -
                have "B \<notin> (dom (\<tau>' (next_time 0 \<tau>')))"
                  using \<open>inf_time (to_trans_raw_sig \<tau>) B i = None\<close>
                  using init'_modifies_local_strongest[OF `init' 0 def {} 0 def nand4 \<tau> \<tau>'` `B \<notin> set (signals_from nand4)`]          
                  by (metis \<open>next_time 0 \<tau>' \<le> time\<close> \<open>next_time time \<tau>_res = time\<close> \<open>next_time time
                  \<tau>_res \<le> i\<close> domD domI inf_time_none_iff leD order.trans to_trans_raw_sig_def)
                thus ?thesis
                  unfolding `next_state 0 \<tau>' def = \<sigma>'`[THEN sym] next_state_def Let_def  by simp
              qed
              also have "... = get_state res' B"
              proof -
                have "inf_time (to_trans_raw_sig (\<tau>'(t' := 0))) B time = None"
                  unfolding inf_time_none_iff[THEN sym]
                proof 
                  { fix x 
                    assume " x \<in> dom (to_trans_raw_sig (\<tau>'(t' := 0)) B)"
                    hence "(\<tau>'(t' := 0)) x B \<noteq> None"
                      unfolding dom_def to_trans_raw_sig_def by auto
                    hence "x \<noteq> t'"
                      unfolding fun_upd_def zero_fun_def zero_option_def by auto
                    assume "x \<le> time"
                    have "(\<tau>'(t' := 0)) x B = \<tau>' x B"
                      using `x \<noteq> t'` by auto
                    also have "... = \<tau> x B"
                      using init'_modifies_local_strongest[OF `init' 0 def {} 0 def nand4 \<tau> \<tau>'` `B \<notin> set (signals_from nand4)`]          
                      by auto
                    also have "... = None"
                      using \<open>inf_time (to_trans_raw_sig \<tau>) B i = None\<close> \<open>time < Suc i\<close> 
                      by (metis \<open>next_time time \<tau>_res = time\<close> \<open>next_time time \<tau>_res \<le> i\<close> \<open>x \<le> time\<close>
                      inf_time_noneE2 le_trans to_trans_raw_sig_def zero_option_def)
                    finally have "False"
                      using \<open>(\<tau>'(t' := 0)) x B \<noteq> None\<close> by blast }
                  thus "\<And>x. x \<in> dom (to_trans_raw_sig (\<tau>'(t' := 0)) B) \<Longrightarrow> time < x"
                    using le_less_linear by blast
                qed
                thus ?thesis
                  using get_state_b_simulate_fin_inf_none[OF bigstep2_pre `B \<notin> set (signals_from nand4)`] 
                  by auto
              qed
              finally have "signal_of (def B) \<tau> B i = get_state res' B"
                by auto
              have "time , get_state res' , get_beh' res' , get_beh res', def  \<turnstile> Bsig A \<longrightarrow>\<^sub>b Bv (bval_of (get_state res' A))"
                by (smt \<open>0 , def , {} , 0, def \<turnstile> Bnand (Bsig A) (Bsig B) \<longrightarrow>\<^sub>b x\<close> \<open>signal_of (def A) \<tau> A i =
                get_state res' A\<close> \<open>x = Bv (\<not> (bval_of (def A) \<and> bval_of (def B)))\<close> assms(4) assms(6)
                beval_cases(1) beval_cases(9) beval_raw.intros(1) signal_of_preserve_well_typedness
                styping_def ty.simps(3) type_of.simps(1) type_of.simps(2) val.exhaust_sel)
              moreover have "time , get_state res' , get_beh' res' , get_beh res', def  \<turnstile> Bsig B \<longrightarrow>\<^sub>b Bv (bval_of (get_state res' B))"
                by (smt \<open>time , get_state res' , get_beh' res' , get_beh res', def \<turnstile> Bnand (Bsig A) (Bsig B)
                \<longrightarrow>\<^sub>b x'\<close> \<open>time , get_state res' , get_beh' res' , get_beh res', def \<turnstile> Bsig A \<longrightarrow>\<^sub>b Bv (bval_of
                (get_state res' A))\<close> beval_cases(9) beval_raw.intros(1) beval_raw_deterministic
                val.distinct(1) val.exhaust_sel)
              ultimately have "x' = Bv (\<not> (bval_of (get_state res' A) \<and> bval_of (get_state res' B)))"
                using beval_cases(9)[OF `time , get_state res' , get_beh' res' , get_beh res', def  \<turnstile> Bnand (Bsig A) (Bsig B) \<longrightarrow>\<^sub>b x'`]
                by (smt beval_cases(1) val.distinct(1))
              hence ?thesis
                using \<open>signal_of (def A) \<tau> A i = get_state res' A\<close> \<open>signal_of (def B) \<tau> B i = get_state res' B\<close> \<open>signal_of (def C) (get_beh res) C i = x'\<close> 
                by auto }
            ultimately have ?thesis
              by auto }
          ultimately have ?thesis
            by auto }
        ultimately have ?thesis
          using nat_neq_iff by blast }
    moreover
    { assume "inf_time (to_trans_raw_sig \<tau>) B i \<noteq> None \<and> inf_time (to_trans_raw_sig \<tau>) A i = None"
      then obtain time where "inf_time (to_trans_raw_sig \<tau>) B i = Some time" and "inf_time (to_trans_raw_sig \<tau>) A i = None"
        by blast
      have "next_time 0 \<tau>' \<le> time"
      proof -
        have "next_time 0 \<tau>' = (LEAST n. dom (\<tau>' n) \<noteq> {})"
          unfolding next_time_def using \<open>\<tau>' \<noteq> 0\<close> by auto
        have "\<exists>n. dom (\<tau>' n) \<noteq> {}"
          using \<open>\<tau>' \<noteq> 0\<close> unfolding dom_def zero_fun_def zero_option_def 
          by fastforce
        have "inf_time (to_trans_raw_sig \<tau>) B i = inf_time (to_trans_raw_sig \<tau>') B i"
          using \<open>trans_post_raw C x (def C) \<tau> 0 0 = \<tau>'\<close> inf_time_trans_post by fastforce
        hence "dom (\<tau>' time) \<noteq> {}"
          using \<open>inf_time (to_trans_raw_sig \<tau>) B i  = Some time\<close> unfolding dom_def 
        proof -
          have "\<exists>s. to_trans_raw_sig \<tau>' s time \<noteq> None"
            by (metis Femto_VHDL_raw.keys_def \<open>inf_time (to_trans_raw_sig \<tau>) B i = Some time\<close> \<open>inf_time (to_trans_raw_sig \<tau>) B i = inf_time (to_trans_raw_sig \<tau>') B i\<close> domIff dom_def inf_time_some_exists zero_option_def)
          then show "{s. \<tau>' time s \<noteq> None} \<noteq> {}"
            by (simp add: to_trans_raw_sig_def)
        qed
        hence "(LEAST n. dom (\<tau>' n) \<noteq> {}) \<le> time"
          using Least_le by auto
        thus "next_time 0 \<tau>' \<le> time"
          using \<open>next_time 0 \<tau>' = (LEAST n. dom (\<tau>' n) \<noteq> {})\<close> by linarith
      qed    
      have "time < Suc i"
        using \<open>inf_time (to_trans_raw_sig \<tau>) B i = Some time\<close>  inf_time_at_most by fastforce    
      have "\<exists>res'. time, t' , \<sigma>' , \<gamma>' , 0, def \<turnstile> <nand4 , \<tau>'(t' := 0)> \<leadsto> res' \<and> Suc i, time , get_state res' , get_beh' res' , get_beh res', def \<turnstile> <nand4 , get_trans res'> \<leadsto> res"
        using split_b_simulate_fin[OF bigstep \<open>next_time 0 \<tau>' \<le>time\<close>[unfolded \<open>next_time 0 \<tau>' = t'\<close>] _ trans_removal conc_stmt_wf_nand4]  \<open>time < Suc i\<close>
        by (meson less_or_eq_imp_le zero_fun_def)
      then obtain res' where bigstep2_pre: "time, t' , \<sigma>' , \<gamma>' , 0, def \<turnstile> <nand4 , \<tau>'(t' := 0)> \<leadsto> res'"
        and bigstep2: "Suc i, time , get_state res' , get_beh' res' , get_beh res', def \<turnstile> <nand4 , get_trans res'> \<leadsto> res"
        by auto
      have "B \<notin> set (signals_from nand4)" and "A \<notin> set (signals_from nand4)"
        unfolding nand4_def by auto
      have "t' < time \<or> t' = time"
        using bau bigstep2_pre by blast
      moreover 
      { assume "t' < time"
        moreover have "\<tau>' time B = \<tau> time B" and "\<tau>' time A = \<tau> time A"
          unfolding \<tau>'_def trans_post_raw_def post_raw_def preempt_raw_def by auto
        moreover have "\<tau> time B \<noteq> 0 \<and> \<tau> time A = 0"
          using \<open>inf_time (to_trans_raw_sig \<tau>) B i = Some time\<close>  \<open>inf_time (to_trans_raw_sig \<tau>) A i = None\<close>
          by (metis Femto_VHDL_raw.keys_def domIff dom_def inf_time_noneE2 inf_time_some_exists
          to_trans_raw_sig_def zero_option_def)
        ultimately have "(\<tau>'(t' := 0)) time B \<noteq> 0 \<and> (\<tau>'(t' := 0)) time A = 0"
          by auto
        hence "B \<notin> set (signals_from nand4)"
          unfolding nand4_def by auto
        have "non_stuttering (to_trans_raw_sig \<tau>') def B"
          using init'_preserves_non_stuttering[OF `init' 0 def {} 0 def nand4 \<tau> \<tau>'` _ _ conc_stmt_wf_nand4] assms(7)
          by blast
        hence "non_stuttering (to_trans_raw_sig (\<tau>'(t' := 0))) \<sigma>' B"
          using non_stuttering_next \<open>next_state 0 \<tau>' def = \<sigma>'\<close> \<open>next_time 0 \<tau>' = t'\<close> by fastforce
        hence "get_event res' \<noteq>  {}"
          using get_event_never_empty'[OF bigstep2_pre \<open>B \<notin> set (signals_from nand4)\<close> _ _ _ trans_removal conc_stmt_wf_nand4]
          \<open>t' < time\<close> \<open>(\<tau>'(t' := 0)) time B \<noteq> 0 \<and> (\<tau>'(t' := 0)) time A = 0\<close> by blast
        have "\<not> disjnt {B, A} (get_event res')"
          using get_event_never_empty[OF bigstep2_pre \<open>B \<notin> set (signals_from nand4)\<close> _ _ _ trans_removal conc_stmt_wf_nand4]
          using \<open>t' < time\<close> \<open>non_stuttering (to_trans_raw_sig (\<tau>'(t' := 0))) \<sigma>' B\<close>  
          using \<open>(\<tau>'(t' := 0)) time B \<noteq> 0 \<and> (\<tau>'(t' := 0)) time A = 0\<close> by fastforce
        hence "get_event res' \<noteq>  {} \<and> \<not> disjnt {B, A} (get_event res')"
          by auto }
      moreover 
      { assume "t' = time"
        hence "res' = (time, \<sigma>', \<gamma>', 0, \<tau>'(t' := 0))"
          using bau[OF bigstep2_pre] by auto
        hence "get_event res' = \<gamma>'"
          by auto
        also have "... = next_event 0 \<tau>' def"
          using \<open>next_event 0 \<tau>' def = \<gamma>'\<close> by auto
        also have "... = {sig. def sig \<noteq> next_state 0 \<tau>' def sig} "
          unfolding next_event_alt_def by auto
        also have "... \<noteq> {}"
        proof -
          have "\<tau>' time B = \<tau> time B" and "\<tau>' time A = \<tau> time A"
            unfolding \<tau>'_def trans_post_raw_def post_raw_def preempt_raw_def by auto
          moreover have "\<tau> time B \<noteq> 0 \<and> \<tau> time A = 0"
            using \<open>inf_time (to_trans_raw_sig \<tau>) B i = Some time\<close> \<open>inf_time (to_trans_raw_sig \<tau>) A i = None\<close> 
            by (metis Femto_VHDL_raw.keys_def domIff dom_def inf_time_noneE2 inf_time_some_exists
            to_trans_raw_sig_def zero_option_def)
          ultimately have "\<tau>' time B \<noteq> 0" and " \<tau>' time A =0"
            by auto
          have  "Femto_VHDL_raw.keys (to_trans_raw_sig \<tau> B) \<noteq> {}"
            using \<open>inf_time (to_trans_raw_sig \<tau>) B i = Some time\<close> inf_time_some_exists by force
          moreover have *: "(LEAST k. k \<in> Femto_VHDL_raw.keys (to_trans_raw_sig \<tau> B)) = time"
          proof (rule Least_equality)
            show " time \<in> Femto_VHDL_raw.keys (to_trans_raw_sig \<tau> B)"
              by (meson \<open>inf_time (to_trans_raw_sig \<tau>) B i = Some time\<close> inf_time_some_exists)
          next
            { fix y 
              assume "y < time"
              assume "y \<in> Femto_VHDL_raw.keys (to_trans_raw_sig \<tau> B)"
              hence "\<tau> y B \<noteq> 0"
                unfolding Femto_VHDL_raw.keys_def to_trans_raw_sig_def by auto
              hence "\<tau>' y B \<noteq> 0"
                by (metis \<open>trans_post_raw C x (def C) \<tau> 0 0 = \<tau>'\<close> sig.distinct(3) sig.distinct(5) to_trans_raw_sig_def trans_post_raw_diff_sig)
              with `y < time` have False
                unfolding `t' = time`[THEN sym] `next_time  0 \<tau>' = t'`[THEN sym] 
                by (simp add: next_time_at_least2 zero_fun_def) }
            thus "\<And>y. y \<in> Femto_VHDL_raw.keys (to_trans_raw_sig \<tau> B) \<Longrightarrow> time \<le> y"
              using not_less by blast
          qed
          moreover have "the (to_trans_raw_sig \<tau> B (LEAST k. k \<in> Femto_VHDL_raw.keys (to_trans_raw_sig \<tau> B))) = next_state 0 \<tau>' def B"
            unfolding * next_state_def 
            by (metis \<open>\<tau>' time B = \<tau> time B\<close> \<open>\<tau>' time B \<noteq> 0\<close> \<open>next_time 0 \<tau>' = t'\<close> \<open>t' = time\<close> comp_apply domIff override_on_apply_in to_trans_raw_sig_def zero_option_def) 
          ultimately show ?thesis
            using assms(7)[unfolded non_stuttering_def] by auto
        qed
        finally have "get_event res' \<noteq>  {}"
          by auto
        have "\<not> disjnt {B, A} (get_event res')"
        proof -
          have "\<tau>' time B = \<tau> time B" and "\<tau>' time A = \<tau> time A"
            unfolding \<tau>'_def trans_post_raw_def post_raw_def preempt_raw_def by auto
          moreover have "\<tau> time B \<noteq> 0 \<and> \<tau> time A = 0"
            using \<open>inf_time (to_trans_raw_sig \<tau>) B i = Some time\<close> \<open>inf_time (to_trans_raw_sig \<tau>) A i = None\<close> 
            by (metis Femto_VHDL_raw.keys_def domIff dom_def inf_time_noneE2 inf_time_some_exists to_trans_raw_sig_def zero_option_def)
          ultimately have "\<tau>' time B \<noteq> 0 " and " \<tau>' time A = 0"
            by auto
          moreover have "\<tau>' time B = \<tau> time B"
            using \<open>\<tau>' time B = \<tau> time B\<close> \<open>\<tau>' time A = \<tau> time A\<close> calculation(2) by blast
          moreover have  "Femto_VHDL_raw.keys (to_trans_raw_sig \<tau> B) \<noteq> {}"
            using \<open>inf_time (to_trans_raw_sig \<tau>) B i = Some time\<close> \<open>inf_time (to_trans_raw_sig \<tau>) A i = None\<close> calculation(2) inf_time_some_exists by force
          moreover have *: "(LEAST k. k \<in> Femto_VHDL_raw.keys (to_trans_raw_sig \<tau> B)) = time"
          proof (rule Least_equality)
            show " time \<in> Femto_VHDL_raw.keys (to_trans_raw_sig \<tau> B)"
              by (metis Femto_VHDL_raw.keys_def calculation(1) calculation(3) domIff dom_def to_trans_raw_sig_def zero_option_def)
          next
            { fix y 
              assume "y < time"
              assume "y \<in> Femto_VHDL_raw.keys (to_trans_raw_sig \<tau> B)"
              hence "\<tau> y B \<noteq> 0"
                unfolding Femto_VHDL_raw.keys_def to_trans_raw_sig_def by auto
              hence "\<tau>' y B \<noteq> 0"
                by (metis \<open>trans_post_raw C x (def C) \<tau> 0 0 = \<tau>'\<close> calculation(2) sig.distinct(3) sig.distinct(5) to_trans_raw_sig_def trans_post_raw_diff_sig)
              with `y < time` have False
                unfolding `t' = time`[THEN sym] `next_time  0 \<tau>' = t'`[THEN sym] 
                by (simp add: next_time_at_least2 zero_fun_def) }
            thus "\<And>y. y \<in> Femto_VHDL_raw.keys (to_trans_raw_sig \<tau> B) \<Longrightarrow> time \<le> y"
              using not_less by blast
          qed
          moreover have "the (to_trans_raw_sig \<tau> B (LEAST k. k \<in> Femto_VHDL_raw.keys (to_trans_raw_sig \<tau> B))) = next_state 0 \<tau>' def B"
            unfolding * next_state_def 
            by (metis \<open>next_time 0 \<tau>' = t'\<close> \<open>t' = time\<close> calculation(1) calculation(3) comp_apply domIff override_on_apply_in to_trans_raw_sig_def zero_option_def) 
          ultimately show ?thesis
            by (metis (full_types) \<open>get_beh' res' = \<gamma>'\<close> \<open>next_event 0 \<tau>' def = \<gamma>'\<close> assms(7) disjnt_insert1 next_state_fixed_point non_stuttering_def)
        qed 
        hence "get_event res' \<noteq> {} \<and> \<not> disjnt {B, A} (get_event res')"
          using \<open>get_beh' res' \<noteq> {}\<close> by blast }
      ultimately have "get_event res' \<noteq> {} \<and> \<not> disjnt {B, A} (get_event res')"
        by auto
      hence " \<not> quiet (get_trans res') (get_event res')" and "\<not> disjnt {B, A} (get_event res')"
        by (simp add: quiet_def)+
      then obtain \<tau>_res where "time, get_state res', get_event res', get_beh res', def \<turnstile> <nand4, get_trans res'> \<longrightarrow>\<^sub>c \<tau>_res"
        using bau[OF bigstep2]  using \<open>time < Suc i\<close> by force
      have "next_time time \<tau>_res \<le> Suc i \<or> Suc i < next_time time \<tau>_res"
        by auto
      moreover
      { assume "Suc i < next_time time \<tau>_res"
        hence " res = (Suc i, get_state res', {}, Femto_VHDL_raw.add_to_beh2 (get_state res') (get_beh res') time def, \<tau>_res) "
          using bau[OF bigstep2] `\<not> quiet (get_trans res') (get_event res')` `time < Suc i` 
          by (smt \<open>time , get_state res' , get_beh' res' , get_beh res', def \<turnstile> <nand4 , get_trans
          res'> \<longrightarrow>\<^sub>c \<tau>_res\<close> b_conc_exec_deterministic less_irrefl_nat not_le)
        hence gb_res: "get_beh res =  Femto_VHDL_raw.add_to_beh2 (get_state res') (get_beh res') time def"
          by auto
        have "time \<le> i"
          using \<open>time < Suc i\<close> less_Suc_eq_le by blast
        have "\<forall>n>time. get_beh res' n C = 0"
          by (metis b_simulate_fin_preserves_hist bigstep2_pre trans_removal zero_fun_def)
        hence "signal_of (def C) (get_beh res) C i = get_state res' C"
          using signal_of_add_to_beh2'[OF `time \<le> i` ] unfolding gb_res by auto
        have "signal_of (def B) \<tau> B i  = signal_of (def B) \<tau>' B i"
          using init'_modifies_local_strongest[OF `init' 0 def {} 0 def nand4 \<tau> \<tau>'` `B \<notin> set (signals_from nand4)`]
          using \<open>trans_post_raw C x (def C) \<tau> 0 0 = \<tau>'\<close> signal_of_trans_post by fastforce
        also have "... = signal_of (\<sigma>' B) \<tau>' B i"
          by (metis \<open>inf_time (to_trans_raw_sig \<tau>) B i = Some time\<close> \<open>trans_post_raw C x (def C) \<tau> 0 0 = \<tau>'\<close> comp_apply option.simps(5) sig.distinct(5) signal_of_trans_post to_signal_def)
        also have "... = signal_of (\<sigma>' B) (\<tau>'(t':=0)) B i"
          by (smt \<open>next_state 0 \<tau>' def = \<sigma>'\<close> \<open>next_time 0 \<tau>' = t'\<close> comp_apply next_state_def next_time_at_least2 override_on_apply_in signal_of_rem_curr_trans_at_t)
        also have "... = signal_of (get_state res' B) (get_trans res') B i"
          using bau_signal_of[OF bigstep2_pre `B \<notin> set (signals_from nand4)` `time \<le> i` trans_removal]
          by blast
        also have "... = get_state res' B"
          by (rule signal_of_def)
             (metis (no_types, lifting) Suc_lessD \<open>B \<notin> set (signals_from nand4)\<close> \<open>Suc i < next_time
             time \<tau>_res\<close> \<open>time , get_state res' , get_beh' res' , get_beh res', def \<turnstile> <nand4 ,
             get_trans res'> \<longrightarrow>\<^sub>c \<tau>_res\<close> antisym_conv2 b_conc_exec_modifies_local_strongest
             dual_order.strict_trans next_time_at_least2 zero_fun_def)
        finally have "signal_of (def B) \<tau> B i = get_state res' B"
          by auto
        have "signal_of (def A) \<tau> A i  = def A"
          using `inf_time (to_trans_raw_sig \<tau>) A i = None` 
          by (simp add: to_signal_def)
        also have "... = \<sigma>' A"
        proof -
          have "A \<notin> (dom (\<tau>' (next_time 0 \<tau>')))"
            using \<open>inf_time (to_trans_raw_sig \<tau>) A i = None\<close>
            using init'_modifies_local_strongest[OF `init' 0 def {} 0 def nand4 \<tau> \<tau>'` `A \<notin> set (signals_from nand4)`]          
            by (metis \<open>\<And>thesis. (\<And>time. \<lbrakk>inf_time (to_trans_raw_sig \<tau>) B i = Some time; inf_time
            (to_trans_raw_sig \<tau>) A i = None\<rbrakk> \<Longrightarrow> thesis) \<Longrightarrow> thesis\<close> \<open>next_time 0 \<tau>' = t'\<close> \<open>t' < time \<or> t'
            = time\<close> \<open>time \<le> i\<close> domIff dom_def inf_time_noneE2 not_le order.strict_trans
            to_trans_raw_sig_def zero_option_def)
          thus ?thesis
            unfolding `next_state 0 \<tau>' def = \<sigma>'`[THEN sym] next_state_def Let_def  by simp
        qed
        also have "... = get_state res' A"
        proof -
          have "inf_time (to_trans_raw_sig (\<tau>'(t' := 0))) A time = None"
            unfolding inf_time_none_iff[THEN sym]
          proof 
            { fix x 
              assume " x \<in> dom (to_trans_raw_sig (\<tau>'(t' := 0)) A)"
              hence "(\<tau>'(t' := 0)) x A \<noteq> None"
                unfolding dom_def to_trans_raw_sig_def by auto
              hence "x \<noteq> t'"
                unfolding fun_upd_def zero_fun_def zero_option_def by auto
              assume "x \<le> time"
              have "(\<tau>'(t' := 0)) x A = \<tau>' x A"
                using `x \<noteq> t'` by auto
              also have "... = \<tau> x A"
                using init'_modifies_local_strongest[OF `init' 0 def {} 0 def nand4 \<tau> \<tau>'` `A \<notin> set (signals_from nand4)`]          
                by auto
              also have "... = None"
                using \<open>inf_time (to_trans_raw_sig \<tau>) A i = None\<close> \<open>time \<le> i\<close> 
                by (metis \<open>x \<le> time\<close> inf_time_noneE2 le_less_trans not_le to_trans_raw_sig_def zero_option_def) 
              finally have "False"
                using \<open>(\<tau>'(t' := 0)) x A \<noteq> None\<close> by blast }
            thus "\<And>x. x \<in> dom (to_trans_raw_sig (\<tau>'(t' := 0)) A) \<Longrightarrow> time < x"
              using le_less_linear by blast
          qed
          thus ?thesis
            using get_state_b_simulate_fin_inf_none[OF bigstep2_pre `A \<notin> set (signals_from nand4)`] 
            by auto
        qed
        finally have "signal_of (def A) \<tau> A i = get_state res' A"
          by auto
        have "time , get_state res' , get_event res' , get_beh res', def  \<turnstile> <Bassign_trans C (Bnand (Bsig A) (Bsig B)) 0 , get_trans res'> \<longrightarrow>\<^sub>s \<tau>_res"
          using conc_cases(1)[OF `time, get_state res', get_event res', get_beh res', def \<turnstile> <nand4, get_trans res'> \<longrightarrow>\<^sub>c \<tau>_res`[unfolded nand4_def]]
          `\<not> disjnt {B, A} (get_event res')` by auto
        obtain x' where " time , get_state res' , get_beh' res' , get_beh res', def  \<turnstile> Bnand (Bsig A) (Bsig B) \<longrightarrow>\<^sub>b x'" and 
          \<tau>_res_def: " trans_post_raw C x' (get_state res' C) (get_trans res') time 0 = \<tau>_res"
          using seq_cases_trans[OF `time , get_state res' , get_event res' , get_beh res', def  \<turnstile> <Bassign_trans C (Bnand (Bsig A) (Bsig B)) 0 , get_trans res'> \<longrightarrow>\<^sub>s \<tau>_res`]
          by blast
        have "time , get_state res' , get_beh' res' , get_beh res', def  \<turnstile> Bsig B \<longrightarrow>\<^sub>b Bv (bval_of (get_state res' B))"
          by (smt \<open>0 , def , {} , 0, def \<turnstile> Bnand (Bsig A) (Bsig B) \<longrightarrow>\<^sub>b x\<close> \<open>signal_of (def B) \<tau> B i =
          get_state res' B\<close> \<open>x = Bv (\<not> (bval_of (def A) \<and> bval_of (def B)))\<close> assms(4) assms(6)
          beval_cases(1) beval_cases(9) beval_raw.intros(1) signal_of_preserve_well_typedness
          styping_def ty.simps(3) type_of.simps(1) type_of.simps(2) val.exhaust_sel)
        moreover have "time , get_state res' , get_beh' res' , get_beh res', def  \<turnstile> Bsig A \<longrightarrow>\<^sub>b Bv (bval_of (get_state res' A))"
          by (smt \<open>time , get_state res' , get_beh' res' , get_beh res', def \<turnstile> Bnand (Bsig A) (Bsig B)
          \<longrightarrow>\<^sub>b x'\<close> \<open>time , get_state res' , get_beh' res' , get_beh res', def \<turnstile> Bsig B \<longrightarrow>\<^sub>b Bv (bval_of
          (get_state res' B))\<close> beval_cases(9) beval_raw.intros(1) beval_raw_deterministic
          val.distinct(1) val.exhaust_sel)
        ultimately have "x' = Bv (\<not> (bval_of (get_state res' B) \<and> bval_of (get_state res' A)))"
          using beval_cases(9)[OF `time , get_state res' , get_beh' res' , get_beh res', def  \<turnstile> Bnand (Bsig A) (Bsig B) \<longrightarrow>\<^sub>b x'`]
          by (smt beval_cases(1) val.distinct(1))
        have "\<not> post_necessary_raw 0 (get_trans res') time C x' (get_state res' C)"
        proof (rule ccontr)
          assume "\<not> \<not> post_necessary_raw 0 (get_trans res') time C x' (get_state res' C)"
          hence "post_necessary_raw 0 (get_trans res') time C x' (get_state res' C)"
            by auto
          hence "\<tau>_res time C = post_raw C x' (get_trans res') (time + 0) time C"
            unfolding \<tau>_res_def[THEN sym] trans_post_raw_def by auto
          hence "next_time time \<tau>_res = time"
            by (metis (no_types, lifting) \<open>Suc i < next_time time \<tau>_res\<close> \<open>time < Suc i\<close>
            add.right_neutral dual_order.strict_trans fun_upd_same next_time_at_least2
            option.distinct(1) post_raw_def zero_fun_def zero_option_def)
          thus "False"
            using `Suc i < next_time time \<tau>_res`  using \<open>time < Suc i\<close> by linarith
        qed
        moreover have "\<not> (\<exists>i\<le>time + 0 - 1. get_trans res' i C = Some x')"
          using b_simulate_fin_preserve_trans_removal[OF bigstep2_pre trans_removal] 
          by (metis (no_types, hide_lams) Suc_diff_1 \<open>t' < time \<or> t' = time\<close> add.right_neutral
          b_simulate_fin.intros(4) b_simulate_fin_deterministic bigstep2_pre comp_eq_dest_lhs
          diff_le_self fun_upd_same le_imp_less_Suc not_gr_zero not_le not_less_zero
          option.distinct(1) snd_conv zero_fun_def zero_option_def)
        ultimately have "x' = get_state res' C"
          unfolding post_necessary_raw_correctness by blast
        hence "bval_of (get_state res' C) \<longleftrightarrow> \<not> (bval_of (get_state res' B) \<and> bval_of (get_state res' A))"
          using `x' = Bv (\<not> (bval_of (get_state res' B) \<and> bval_of (get_state res' A)))`
          using val.sel(1) by presburger
        hence ?thesis
          using `signal_of (def B) \<tau> B i = get_state res' B` `signal_of (def A) \<tau> A i = get_state res' A`
          `signal_of (def C) (get_beh res) C i = get_state res' C` by auto }
      moreover
      { assume "next_time time \<tau>_res = Suc i"
        hence bigstep3: "Suc i, next_time time \<tau>_res , next_state time \<tau>_res (get_state res') , next_event time \<tau>_res (get_state res') , Femto_VHDL_raw.add_to_beh2 (get_state res') (get_beh res') time def, def \<turnstile> <nand4 , \<tau>_res (next_time time \<tau>_res := 0)> \<leadsto> res"
          using bau[OF bigstep2] 
          by (smt \<open>\<not> quiet (get_trans res') (get_beh' res')\<close> \<open>time , get_state res' , get_beh' res' ,
          get_beh res', def \<turnstile> <nand4 , get_trans res'> \<longrightarrow>\<^sub>c \<tau>_res\<close> \<open>time < Suc i\<close> bigstep2
          calculation(1) case_bau less_irrefl_nat)
        have "res = (Suc i, next_state time \<tau>_res (get_state res'), next_event time \<tau>_res (get_state res'), Femto_VHDL_raw.add_to_beh2 (get_state res') (get_beh res') time def, \<tau>_res (next_time time \<tau>_res := 0))"
          using bau[OF bigstep3] `next_time time \<tau>_res = Suc i` by auto
        hence gb_res: "get_beh res = Femto_VHDL_raw.add_to_beh2 (get_state res') (get_beh res') time def"
          by auto
        have "time \<le> i"
          using \<open>time < Suc i\<close> less_Suc_eq_le by blast
        have "\<forall>n>time. get_beh res' n C = 0"
          by (metis b_simulate_fin_preserves_hist bigstep2_pre trans_removal zero_fun_def)
        hence "signal_of (def C) (get_beh res) C i = get_state res' C"
          using signal_of_add_to_beh2'[OF `time \<le> i` ] unfolding gb_res by auto
        have "signal_of (def B) \<tau> B i  = signal_of (def B) \<tau>' B i"
          using init'_modifies_local_strongest[OF `init' 0 def {} 0 def nand4 \<tau> \<tau>'` `B \<notin> set (signals_from nand4)`]
          using \<open>trans_post_raw C x (def C) \<tau> 0 0 = \<tau>'\<close> signal_of_trans_post by fastforce
        also have "... = signal_of (\<sigma>' B) \<tau>' B i"
          by (metis \<open>inf_time (to_trans_raw_sig \<tau>) B i = Some time\<close> \<open>trans_post_raw C x (def C) \<tau> 0 0 = \<tau>'\<close> comp_apply option.simps(5) sig.simps(6) signal_of_trans_post to_signal_def)
        also have "... = signal_of (\<sigma>' B) (\<tau>'(t':=0)) B i"
          by (smt \<open>next_state 0 \<tau>' def = \<sigma>'\<close> \<open>next_time 0 \<tau>' = t'\<close> comp_apply next_state_def next_time_at_least2 override_on_apply_in signal_of_rem_curr_trans_at_t)
        also have "... = signal_of (get_state res' B) (get_trans res') B i"
          using bau_signal_of[OF bigstep2_pre `B \<notin> set (signals_from nand4)` `time \<le> i` trans_removal]
          by blast
        also have "... = get_state res' B"
          by (metis (no_types, lifting) \<open>B \<notin> set (signals_from nand4)\<close> \<open>next_time time \<tau>_res = Suc i\<close> \<open>time , get_state res' , get_beh' res' , get_beh res', def \<turnstile> <nand4 , get_trans res'> \<longrightarrow>\<^sub>c \<tau>_res\<close> b_conc_exec_modifies_local_strongest dual_order.strict_trans2 lessI next_time_at_least2 signal_of_def zero_fun_def)
        finally have "signal_of (def B) \<tau> B i = get_state res' B"
          by auto
        have "signal_of (def A) \<tau> A i  = def A"
          using `inf_time (to_trans_raw_sig \<tau>) A i = None` 
          by (simp add: to_signal_def)
        also have "... = \<sigma>' A"
        proof -
          have "A \<notin> (dom (\<tau>' (next_time 0 \<tau>')))"
            using \<open>inf_time (to_trans_raw_sig \<tau>) A i = None\<close>
            using init'_modifies_local_strongest[OF `init' 0 def {} 0 def nand4 \<tau> \<tau>'` `A \<notin> set (signals_from nand4)`]          
            by (metis \<open>\<And>thesis. (\<And>time. \<lbrakk>inf_time (to_trans_raw_sig \<tau>) B i = Some time; inf_time
            (to_trans_raw_sig \<tau>) A i = None\<rbrakk> \<Longrightarrow> thesis) \<Longrightarrow> thesis\<close> \<open>next_time 0 \<tau>' = t'\<close> \<open>t' < time \<or> t'
            = time\<close> \<open>time \<le> i\<close> domIff dom_def inf_time_noneE2 not_le order.strict_trans
            to_trans_raw_sig_def zero_option_def)
          thus ?thesis
            unfolding `next_state 0 \<tau>' def = \<sigma>'`[THEN sym] next_state_def Let_def  by simp
        qed
        also have "... = get_state res' A"
        proof -
          have "inf_time (to_trans_raw_sig (\<tau>'(t' := 0))) A time = None"
            unfolding inf_time_none_iff[THEN sym]
          proof 
            { fix x 
              assume " x \<in> dom (to_trans_raw_sig (\<tau>'(t' := 0)) A)"
              hence "(\<tau>'(t' := 0)) x A \<noteq> None"
                unfolding dom_def to_trans_raw_sig_def by auto
              hence "x \<noteq> t'"
                unfolding fun_upd_def zero_fun_def zero_option_def by auto
              assume "x \<le> time"
              have "(\<tau>'(t' := 0)) x A = \<tau>' x A"
                using `x \<noteq> t'` by auto
              also have "... = \<tau> x A"
                using init'_modifies_local_strongest[OF `init' 0 def {} 0 def nand4 \<tau> \<tau>'` `A \<notin> set (signals_from nand4)`]          
                by auto
              also have "... = None"
                using \<open>inf_time (to_trans_raw_sig \<tau>) A i = None\<close> \<open>time \<le> i\<close> 
                by (metis \<open>x \<le> time\<close> inf_time_noneE2 le_less_trans not_le to_trans_raw_sig_def zero_option_def) 
              finally have "False"
                using \<open>(\<tau>'(t' := 0)) x A \<noteq> None\<close> by blast }
            thus "\<And>x. x \<in> dom (to_trans_raw_sig (\<tau>'(t' := 0)) A) \<Longrightarrow> time < x"
              using le_less_linear by blast
          qed
          thus ?thesis
            using get_state_b_simulate_fin_inf_none[OF bigstep2_pre `A \<notin> set (signals_from nand4)`] 
            by auto
        qed
        finally have "signal_of (def A) \<tau> A i = get_state res' A"
          by auto
        have "time , get_state res' , get_event res' , get_beh res', def  \<turnstile> <Bassign_trans C (Bnand (Bsig A) (Bsig B)) 0 , get_trans res'> \<longrightarrow>\<^sub>s \<tau>_res"
          using conc_cases(1)[OF `time, get_state res', get_event res', get_beh res', def \<turnstile> <nand4, get_trans res'> \<longrightarrow>\<^sub>c \<tau>_res`[unfolded nand4_def]]
          `\<not> disjnt {B, A} (get_event res')` by auto
        obtain x' where " time , get_state res' , get_beh' res' , get_beh res', def  \<turnstile> Bnand (Bsig A) (Bsig B) \<longrightarrow>\<^sub>b x'" and 
          \<tau>_res_def: " trans_post_raw C x' (get_state res' C) (get_trans res') time 0 = \<tau>_res"
          using seq_cases_trans[OF `time , get_state res' , get_event res' , get_beh res', def  \<turnstile> <Bassign_trans C (Bnand (Bsig A) (Bsig B)) 0 , get_trans res'> \<longrightarrow>\<^sub>s \<tau>_res`]
          by blast
        have "time , get_state res' , get_beh' res' , get_beh res', def  \<turnstile> Bsig B \<longrightarrow>\<^sub>b Bv (bval_of (get_state res' B))"
          by (smt \<open>0 , def , {} , 0, def \<turnstile> Bnand (Bsig A) (Bsig B) \<longrightarrow>\<^sub>b x\<close> \<open>signal_of (def B) \<tau> B i =
          get_state res' B\<close> \<open>x = Bv (\<not> (bval_of (def A) \<and> bval_of (def B)))\<close> assms(4) assms(6)
          beval_cases(1) beval_cases(9) beval_raw.intros(1) signal_of_preserve_well_typedness
          styping_def ty.simps(3) type_of.simps(1) type_of.simps(2) val.exhaust_sel)
        moreover have "time , get_state res' , get_beh' res' , get_beh res', def  \<turnstile> Bsig A \<longrightarrow>\<^sub>b Bv (bval_of (get_state res' A))"
          by (smt \<open>time , get_state res' , get_beh' res' , get_beh res', def \<turnstile> Bnand (Bsig A) (Bsig B)
          \<longrightarrow>\<^sub>b x'\<close> \<open>time , get_state res' , get_beh' res' , get_beh res', def \<turnstile> Bsig B \<longrightarrow>\<^sub>b Bv (bval_of
          (get_state res' B))\<close> beval_cases(9) beval_raw.intros(1) beval_raw_deterministic
          val.distinct(1) val.exhaust_sel)
        ultimately have "x' = Bv (\<not> (bval_of (get_state res' B) \<and> bval_of (get_state res' A)))"
          using beval_cases(9)[OF `time , get_state res' , get_beh' res' , get_beh res', def  \<turnstile> Bnand (Bsig A) (Bsig B) \<longrightarrow>\<^sub>b x'`]
          by (smt beval_cases(1) val.distinct(1))
        have "\<not> post_necessary_raw 0 (get_trans res') time C x' (get_state res' C)"
        proof (rule ccontr)
          assume "\<not> \<not> post_necessary_raw 0 (get_trans res') time C x' (get_state res' C)"
          hence "post_necessary_raw 0 (get_trans res') time C x' (get_state res' C)"
            by auto
          hence "\<tau>_res time C = post_raw C x' (get_trans res') (time + 0) time C"
            unfolding \<tau>_res_def[THEN sym] trans_post_raw_def by auto
          hence "next_time time \<tau>_res = time"
            by (metis (no_types, lifting) \<open> next_time time \<tau>_res = Suc i\<close> \<open>time < Suc i\<close>
            add.right_neutral dual_order.strict_trans fun_upd_same next_time_at_least2
            option.distinct(1) post_raw_def zero_fun_def zero_option_def)
          thus "False"
            using `next_time time \<tau>_res = Suc i`  using \<open>time < Suc i\<close> by linarith
        qed
        moreover have "\<not> (\<exists>i\<le>time + 0 - 1. get_trans res' i C = Some x')"
          using b_simulate_fin_preserve_trans_removal[OF bigstep2_pre trans_removal] 
          by (metis (no_types, hide_lams) Suc_diff_1 \<open>t' < time \<or> t' = time\<close> add.right_neutral
          b_simulate_fin.intros(4) b_simulate_fin_deterministic bigstep2_pre comp_eq_dest_lhs
          diff_le_self fun_upd_same le_imp_less_Suc not_gr_zero not_le not_less_zero
          option.distinct(1) snd_conv zero_fun_def zero_option_def)
        ultimately have "x' = get_state res' C"
          unfolding post_necessary_raw_correctness by blast
        hence "bval_of (get_state res' C) \<longleftrightarrow> \<not> (bval_of (get_state res' B) \<and> bval_of (get_state res' A))"
          using `x' = Bv (\<not> (bval_of (get_state res' B) \<and> bval_of (get_state res' A)))`
          using val.sel(1) by presburger
        hence ?thesis
          using `signal_of (def B) \<tau> B i = get_state res' B` `signal_of (def A) \<tau> A i = get_state res' A`
          `signal_of (def C) (get_beh res) C i = get_state res' C` by auto }
        moreover
        { assume "next_time time \<tau>_res < Suc i"
          hence bigstep3: "Suc i, next_time time \<tau>_res , next_state time \<tau>_res (get_state res') , next_event time \<tau>_res (get_state res') , Femto_VHDL_raw.add_to_beh2 (get_state res') (get_beh res') time def, def \<turnstile> <nand4 , \<tau>_res (next_time time \<tau>_res := 0)> \<leadsto> res"
            using bau[OF bigstep2] 
            by (smt \<open>\<not> quiet (get_trans res') (get_beh' res')\<close> \<open>time , get_state res' , get_beh' res' , get_beh res', def \<turnstile> <nand4 , get_trans res'> \<longrightarrow>\<^sub>c \<tau>_res\<close> \<open>time < Suc i\<close> bigstep2 case_bau nat_less_le)
          have "\<tau>_res = 0 \<or> \<tau>_res \<noteq> 0"
            by auto
          moreover
          { assume "\<tau>_res = 0"
            hence "next_event time \<tau>_res (get_state res') = {}"
            proof -
              have "next_state time \<tau>_res (get_state res') = get_state res'"
                using `\<tau>_res = 0` unfolding next_state_def Let_def  by (simp add: zero_fun_def zero_option_def)
              thus ?thesis
                unfolding next_event_alt_def  by auto
            qed
            hence "quiet (\<tau>_res (next_time time \<tau>_res := 0)) (next_event time \<tau>_res (get_state res'))"
              using `\<tau>_res = 0`  by (simp add: fun_upd_idem_iff quiet_def zero_fun_def)
            hence "res = (Suc i, next_state time \<tau>_res (get_state res'), next_event time \<tau>_res (get_state res'), Femto_VHDL_raw.add_to_beh2 (get_state res') (get_beh res') time def, 0)"
              using bau[OF bigstep3] `next_time time \<tau>_res < Suc i` by auto
            hence gb_res: "get_beh res = Femto_VHDL_raw.add_to_beh2 (get_state res') (get_beh res') time def"
              by auto
            have "time \<le> i"
              using \<open>time < Suc i\<close> less_Suc_eq_le by blast
            have "\<forall>n>time. get_beh res' n C = 0"
              by (metis b_simulate_fin_preserves_hist bigstep2_pre trans_removal zero_fun_def)
            hence "signal_of (def C) (get_beh res) C i = get_state res' C"
              using signal_of_add_to_beh2'[OF `time \<le> i` ] unfolding gb_res by auto
            have "signal_of (def B) \<tau> B i  = signal_of (def B) \<tau>' B i"
              using init'_modifies_local_strongest[OF `init' 0 def {} 0 def nand4 \<tau> \<tau>'` `B \<notin> set (signals_from nand4)`]
              using \<open>trans_post_raw C x (def C) \<tau> 0 0 = \<tau>'\<close> signal_of_trans_post by fastforce
            also have "... = signal_of (\<sigma>' B) \<tau>' B i"
              by (metis \<open>\<And>thesis. (\<And>time. \<lbrakk>inf_time (to_trans_raw_sig \<tau>) B i = Some time; inf_time (to_trans_raw_sig \<tau>) A i = None\<rbrakk> \<Longrightarrow> thesis) \<Longrightarrow> thesis\<close> \<open>trans_post_raw C x (def C) \<tau> 0 0 = \<tau>'\<close> comp_apply option.simps(5) sig.simps(6) signal_of_trans_post to_signal_def)
            also have "... = signal_of (\<sigma>' B) (\<tau>'(t':=0)) B i"
              by (smt \<open>next_state 0 \<tau>' def = \<sigma>'\<close> \<open>next_time 0 \<tau>' = t'\<close> comp_apply next_state_def next_time_at_least2 override_on_apply_in signal_of_rem_curr_trans_at_t)
            also have "... = signal_of (get_state res' B) (get_trans res') B i"
              using bau_signal_of[OF bigstep2_pre `B \<notin> set (signals_from nand4)` `time \<le> i` trans_removal]
              by blast
            also have "... = get_state res' B"
              by (metis (no_types, hide_lams) \<open>B \<notin> set (signals_from nand4)\<close> \<open>\<tau>_res = 0\<close> \<open>time , get_state res' , get_beh' res' , get_beh res', def \<turnstile> <nand4 , get_trans res'> \<longrightarrow>\<^sub>c \<tau>_res\<close> b_conc_exec_modifies_local_strongest signal_of_def zero_fun_def)
            finally have "signal_of (def B) \<tau> B i = get_state res' B"
              by auto
            have "signal_of (def A) \<tau> A i  = def A"
              using `inf_time (to_trans_raw_sig \<tau>) A i = None` 
              by (simp add: to_signal_def)
            also have "... = \<sigma>' A"
            proof -
              have "A \<notin> (dom (\<tau>' (next_time 0 \<tau>')))"
                using \<open>inf_time (to_trans_raw_sig \<tau>) A i = None\<close>
                using init'_modifies_local_strongest[OF `init' 0 def {} 0 def nand4 \<tau> \<tau>'` `A \<notin> set (signals_from nand4)`]          
                by (metis \<open>\<And>thesis. (\<And>time. \<lbrakk>inf_time (to_trans_raw_sig \<tau>) B i = Some time; inf_time
                (to_trans_raw_sig \<tau>) A i = None\<rbrakk> \<Longrightarrow> thesis) \<Longrightarrow> thesis\<close> \<open>next_time 0 \<tau>' = t'\<close> \<open>t' < time \<or> t'
                = time\<close> \<open>time \<le> i\<close> domIff dom_def inf_time_noneE2 not_le order.strict_trans
                to_trans_raw_sig_def zero_option_def)
              thus ?thesis
                unfolding `next_state 0 \<tau>' def = \<sigma>'`[THEN sym] next_state_def Let_def  by simp
            qed
            also have "... = get_state res' A"
            proof -
              have "inf_time (to_trans_raw_sig (\<tau>'(t' := 0))) A time = None"
                unfolding inf_time_none_iff[THEN sym]
              proof 
                { fix x 
                  assume " x \<in> dom (to_trans_raw_sig (\<tau>'(t' := 0)) A)"
                  hence "(\<tau>'(t' := 0)) x A \<noteq> None"
                    unfolding dom_def to_trans_raw_sig_def by auto
                  hence "x \<noteq> t'"
                    unfolding fun_upd_def zero_fun_def zero_option_def by auto
                  assume "x \<le> time"
                  have "(\<tau>'(t' := 0)) x A = \<tau>' x A"
                    using `x \<noteq> t'` by auto
                  also have "... = \<tau> x A"
                    using init'_modifies_local_strongest[OF `init' 0 def {} 0 def nand4 \<tau> \<tau>'` `A \<notin> set (signals_from nand4)`]          
                    by auto
                  also have "... = None"
                    using \<open>inf_time (to_trans_raw_sig \<tau>) A i = None\<close> \<open>time \<le> i\<close> 
                    by (metis \<open>x \<le> time\<close> inf_time_noneE2 le_less_trans not_le to_trans_raw_sig_def zero_option_def) 
                  finally have "False"
                    using \<open>(\<tau>'(t' := 0)) x A \<noteq> None\<close> by blast }
                thus "\<And>x. x \<in> dom (to_trans_raw_sig (\<tau>'(t' := 0)) A) \<Longrightarrow> time < x"
                  using le_less_linear by blast
              qed
              thus ?thesis
                using get_state_b_simulate_fin_inf_none[OF bigstep2_pre `A \<notin> set (signals_from nand4)`] 
                by auto
            qed
            finally have "signal_of (def A) \<tau> A i = get_state res' A"
              by auto
            have "time , get_state res' , get_event res' , get_beh res', def  \<turnstile> <Bassign_trans C (Bnand (Bsig A) (Bsig B)) 0 , get_trans res'> \<longrightarrow>\<^sub>s \<tau>_res"
              using conc_cases(1)[OF `time, get_state res', get_event res', get_beh res', def \<turnstile> <nand4, get_trans res'> \<longrightarrow>\<^sub>c \<tau>_res`[unfolded nand4_def]]
              `\<not> disjnt {B, A} (get_event res')` by auto
            obtain x' where " time , get_state res' , get_beh' res' , get_beh res', def  \<turnstile> Bnand (Bsig A) (Bsig B) \<longrightarrow>\<^sub>b x'" and 
              \<tau>_res_def: " trans_post_raw C x' (get_state res' C) (get_trans res') time 0 = \<tau>_res"
              using seq_cases_trans[OF `time , get_state res' , get_event res' , get_beh res', def  \<turnstile> <Bassign_trans C (Bnand (Bsig A) (Bsig B)) 0 , get_trans res'> \<longrightarrow>\<^sub>s \<tau>_res`]
              by blast
            have "time , get_state res' , get_beh' res' , get_beh res', def  \<turnstile> Bsig B \<longrightarrow>\<^sub>b Bv (bval_of (get_state res' B))"
              by (smt \<open>0 , def , {} , 0, def \<turnstile> Bnand (Bsig A) (Bsig B) \<longrightarrow>\<^sub>b x\<close> \<open>signal_of (def B) \<tau> B i =
              get_state res' B\<close> \<open>x = Bv (\<not> (bval_of (def A) \<and> bval_of (def B)))\<close> assms(4) assms(6)
              beval_cases(1) beval_cases(9) beval_raw.intros(1) signal_of_preserve_well_typedness
              styping_def ty.simps(3) type_of.simps(1) type_of.simps(2) val.exhaust_sel)
            moreover have "time , get_state res' , get_beh' res' , get_beh res', def  \<turnstile> Bsig A \<longrightarrow>\<^sub>b Bv (bval_of (get_state res' A))"
              by (smt \<open>time , get_state res' , get_beh' res' , get_beh res', def \<turnstile> Bnand (Bsig A) (Bsig B)
              \<longrightarrow>\<^sub>b x'\<close> \<open>time , get_state res' , get_beh' res' , get_beh res', def \<turnstile> Bsig B \<longrightarrow>\<^sub>b Bv (bval_of
              (get_state res' B))\<close> beval_cases(9) beval_raw.intros(1) beval_raw_deterministic
              val.distinct(1) val.exhaust_sel)
            ultimately have "x' = Bv (\<not> (bval_of (get_state res' B) \<and> bval_of (get_state res' A)))"
              using beval_cases(9)[OF `time , get_state res' , get_beh' res' , get_beh res', def  \<turnstile> Bnand (Bsig A) (Bsig B) \<longrightarrow>\<^sub>b x'`]
              by (smt beval_cases(1) val.distinct(1))
            have "\<not> post_necessary_raw 0 (get_trans res') time C x' (get_state res' C)"
            proof (rule ccontr)
              assume "\<not> \<not> post_necessary_raw 0 (get_trans res') time C x' (get_state res' C)"
              hence "post_necessary_raw 0 (get_trans res') time C x' (get_state res' C)"
                by auto
              hence "\<tau>_res time C = post_raw C x' (get_trans res') (time + 0) time C"
                unfolding \<tau>_res_def[THEN sym] trans_post_raw_def by auto
              hence "next_time time \<tau>_res = time"
                by (simp add: \<open>\<tau>_res = 0\<close> post_raw_def zero_fun_def zero_option_def)
              thus "False"
                using `next_time time \<tau>_res < Suc i`  using \<open>time < Suc i\<close> 
                by (simp add: \<open>\<tau>_res = 0\<close>)
            qed
            moreover have "\<not> (\<exists>i\<le>time + 0 - 1. get_trans res' i C = Some x')"
              using b_simulate_fin_preserve_trans_removal[OF bigstep2_pre trans_removal] 
              by (metis (no_types, hide_lams) Suc_diff_1 \<open>t' < time \<or> t' = time\<close> add.right_neutral
              b_simulate_fin.intros(4) b_simulate_fin_deterministic bigstep2_pre comp_eq_dest_lhs
              diff_le_self fun_upd_same le_imp_less_Suc not_gr_zero not_le not_less_zero
              option.distinct(1) snd_conv zero_fun_def zero_option_def)
            ultimately have "x' = get_state res' C"
              unfolding post_necessary_raw_correctness by blast
            hence "bval_of (get_state res' C) \<longleftrightarrow> \<not> (bval_of (get_state res' B) \<and> bval_of (get_state res' A))"
              using `x' = Bv (\<not> (bval_of (get_state res' B) \<and> bval_of (get_state res' A)))`
              using val.sel(1) by presburger
            hence ?thesis
              using `signal_of (def B) \<tau> B i = get_state res' B` `signal_of (def A) \<tau> A i = get_state res' A`
              `signal_of (def C) (get_beh res) C i = get_state res' C` by auto }
          moreover
          { assume "\<tau>_res \<noteq> 0"
            have "time , get_state res' , get_event res' , get_beh res', def  \<turnstile> <Bassign_trans C (Bnand (Bsig A) (Bsig B)) 0 , get_trans res'> \<longrightarrow>\<^sub>s \<tau>_res"
              using conc_cases(1)[OF `time, get_state res', get_event res', get_beh res', def \<turnstile> <nand4, get_trans res'> \<longrightarrow>\<^sub>c \<tau>_res`[unfolded nand4_def]]
              `\<not> disjnt {B, A} (get_event res')` by auto
            obtain x' where " time , get_state res' , get_beh' res' , get_beh res', def  \<turnstile> Bnand (Bsig A) (Bsig B) \<longrightarrow>\<^sub>b x'" and 
              \<tau>_res_def: " trans_post_raw C x' (get_state res' C) (get_trans res') time 0 = \<tau>_res"
              using seq_cases_trans[OF `time , get_state res' , get_event res' , get_beh res', def  \<turnstile> <Bassign_trans C (Bnand (Bsig A) (Bsig B)) 0 , get_trans res'> \<longrightarrow>\<^sub>s \<tau>_res`]
              by blast
            have "\<And>n. n < time \<Longrightarrow> \<tau>_res n = 0"
              using b_conc_exec_preserve_trans_removal[OF `time, get_state res', get_event res', get_beh res', def \<turnstile> <nand4, get_trans res'> \<longrightarrow>\<^sub>c \<tau>_res`]
              b_simulate_fin_preserve_trans_removal[OF bigstep2_pre trans_removal] by auto
            have "next_time time \<tau>_res = time"
            proof (rule ccontr)
              assume "next_time time \<tau>_res \<noteq> time" 
              hence "time < next_time time \<tau>_res"
                by (metis \<open>\<And>n. n < time \<Longrightarrow> \<tau>_res n = 0\<close> nat_less_le next_time_at_least)
              hence "\<tau>_res (next_time time \<tau>_res) C = None"
                unfolding \<tau>_res_def[THEN sym] trans_post_raw_def preempt_raw_def post_raw_def
                by (smt add.right_neutral dual_order.strict_implies_order fun_upd_eqD fun_upd_triv nat_neq_iff)
              have "next_time time \<tau>_res = (LEAST n. dom (\<tau>_res n) \<noteq> {})"
                using `\<tau>_res \<noteq> 0` unfolding next_time_def by auto
              hence "\<tau>_res time = 0"
                using `time < next_time time \<tau>_res`  using next_time_at_least2 by blast
              have "\<exists>n. dom (\<tau>_res n) \<noteq> {}"
                using `\<tau>_res \<noteq> 0` unfolding dom_def zero_fun_def zero_option_def by fastforce
              have "\<tau>_res (next_time time \<tau>_res) \<noteq> 0"
                by (metis (mono_tags, lifting) LeastI \<open>\<exists>n. dom (\<tau>_res n) \<noteq> {}\<close> \<open>next_time time \<tau>_res = (LEAST n. dom (\<tau>_res n) \<noteq> {})\<close> dom_eq_empty_conv zero_map)
              hence "\<tau>_res (next_time time \<tau>_res) B \<noteq> None \<or> \<tau>_res (next_time time \<tau>_res) A \<noteq> None "
                using `\<tau>_res (next_time time \<tau>_res) C = None` unfolding zero_fun_def zero_option_def 
                by (metis sig.exhaust)
              hence "get_trans res' (next_time time \<tau>_res) B \<noteq> None \<or> get_trans res' (next_time time \<tau>_res) A \<noteq> None"
                using b_conc_exec_modifies_local_strongest[OF `time, get_state res', get_event res', get_beh res', def \<turnstile> <nand4, get_trans res'> \<longrightarrow>\<^sub>c \<tau>_res`]
                by (simp add: \<open>B \<notin> set (signals_from nand4)\<close> \<open>A \<notin> set (signals_from nand4)\<close>)
              hence "(\<tau>'(t' := 0)) (next_time time \<tau>_res) B \<noteq> None \<or> (\<tau>'(t' := 0)) (next_time time \<tau>_res) A \<noteq> None"
                using b_simulate_fin_get_trans_gt_maxtime[OF bigstep2_pre `B \<notin> set (signals_from nand4)`]
                using b_simulate_fin_get_trans_gt_maxtime[OF bigstep2_pre `A \<notin> set (signals_from nand4)`]
                by (simp add: \<open>time < next_time time \<tau>_res\<close>)
              hence "\<tau>' (next_time time \<tau>_res) B \<noteq> None \<or> \<tau>' (next_time time \<tau>_res) A \<noteq> None"
                by (metis \<open>\<And>n. n < time \<Longrightarrow> \<tau>_res n = 0\<close> \<open>\<tau>_res (next_time time \<tau>_res) \<noteq> 0\<close> \<open>next_time time \<tau>_res \<noteq> time\<close> \<open>t' < time \<or> t' = time\<close> fun_upd_other)
              hence "\<tau> (next_time time \<tau>_res) B \<noteq> None \<or> \<tau> (next_time time \<tau>_res) A \<noteq> None"
                by (metis \<open>\<And>thesis. (\<And>x. \<lbrakk>0 , def , {} , 0, def \<turnstile> Bnand (Bsig A) (Bsig B) \<longrightarrow>\<^sub>b x;
                trans_post_raw C x (def C) \<tau> 0 0 = \<tau>'\<rbrakk> \<Longrightarrow> thesis) \<Longrightarrow> thesis\<close> sig.distinct(3)
                sig.distinct(5) to_trans_raw_sig_def trans_post_raw_diff_sig)
              thus "False"
                using inf_time_someE[OF \<open>inf_time (to_trans_raw_sig \<tau>) B i = Some time\<close>]
                \<open>time < next_time time \<tau>_res\<close> \<open>next_time time \<tau>_res < Suc i\<close>
                by (metis \<open>inf_time (to_trans_raw_sig \<tau>) A i = None\<close> domIff inf_time_noneE2 less_Suc_eq_le not_le to_trans_raw_sig_def zero_option_def)
            qed
            hence "\<tau>_res time \<noteq> 0"
              using `\<tau>_res \<noteq> 0` unfolding zero_fun_def zero_option_def next_time_def 
              by (metis (mono_tags, lifting) LeastI_ex dom_eq_empty_conv)
            have " get_trans res' time = 0"
              using get_trans_res_maxtime[OF bigstep2_pre ] by auto          
            hence "\<tau>_res time B = 0" and "\<tau>_res time A = 0"
              using b_conc_exec_modifies_local_strongest[OF `time, get_state res', get_event res', get_beh res', def \<turnstile> <nand4, get_trans res'> \<longrightarrow>\<^sub>c \<tau>_res` `B \<notin> set (signals_from nand4)`]
              using b_conc_exec_modifies_local_strongest[OF `time, get_state res', get_event res', get_beh res', def \<turnstile> <nand4, get_trans res'> \<longrightarrow>\<^sub>c \<tau>_res` `A \<notin> set (signals_from nand4)`]
              by (metis zero_fun_def)+
            hence " B \<notin> next_event time \<tau>_res (get_state res')" and " A \<notin> next_event time \<tau>_res (get_state res')"
              unfolding next_event_alt_def next_state_def \<open>next_time time \<tau>_res = time\<close> 
              by (smt domIff mem_Collect_eq override_on_def zero_option_def)+
            hence "disjnt {B, A} (next_event time \<tau>_res (get_state res'))"
              by auto
            have "\<tau>_res time C \<noteq> 0"
            proof (rule ccontr)
              assume "\<not> \<tau>_res time C \<noteq> 0" hence "\<tau>_res time C = 0" by auto
              hence "\<tau>_res time = 0"
                using `\<tau>_res time B = 0` `\<tau>_res time A = 0` 
                unfolding zero_fun_def zero_option_def  by (metis sig.exhaust)
              with `\<tau>_res time \<noteq> 0` show False 
                by auto
            qed
            have "post_necessary_raw 0 (get_trans res') time C x' (get_state res' C)"
            proof (rule ccontr)
              assume "\<not> post_necessary_raw 0 (get_trans res') time C x' (get_state res' C)"
              hence "\<tau>_res time C = 0"
                unfolding \<tau>_res_def[THEN sym] trans_post_raw_def preempt_raw_def by (auto simp add: zero_option_def)
              with `\<tau>_res time C \<noteq> 0` show False
                by auto
            qed
            hence "\<tau>_res time C = Some x'"
              unfolding \<tau>_res_def[THEN sym] trans_post_raw_def post_raw_def by auto
            have "\<not> (\<exists>i\<le>time + 0 - 1. get_trans res' i C = Some x')"
              using b_simulate_fin_preserve_trans_removal[OF bigstep2_pre trans_removal] 
              by (metis (no_types, hide_lams) Suc_diff_1 \<open>t' < time \<or> t' = time\<close> add.right_neutral
              b_simulate_fin.intros(4) b_simulate_fin_deterministic bigstep2_pre comp_eq_dest_lhs
              diff_le_self fun_upd_same le_imp_less_Suc not_gr_zero not_le not_less_zero
              option.distinct(1) snd_conv zero_fun_def zero_option_def)
            hence "get_state res' C \<noteq> x'"
              using `post_necessary_raw 0 (get_trans res') time C x' (get_state res' C)`
              unfolding post_necessary_raw_correctness2 
              by (metis (no_types, lifting) Suc_diff_1 \<open>next_time time \<tau>_res = time\<close> \<open>post_necessary_raw
              0 (get_trans res') time C x' (get_state res' C)\<close> \<tau>_res_def add.right_neutral
              le_imp_less_Suc next_time_at_least2 option.distinct(1) order.asym post_raw_def
              trans_post_raw_def zero_fun_def zero_option_def)
            hence "get_state res'  C \<noteq> the (\<tau>_res time C)"
              by (simp add: \<open>\<tau>_res time C = Some x'\<close>)
            hence "C \<in> (next_event time \<tau>_res (get_state res'))" 
              unfolding next_event_alt_def next_state_def 
              by (smt \<open>\<tau>_res time C \<noteq> 0\<close> \<open>next_time time \<tau>_res = time\<close> comp_def domIff mem_Collect_eq override_on_apply_in zero_option_def)
            hence "next_time time
                \<tau>_res , next_state time \<tau>_res
                         (get_state res') , next_event time \<tau>_res (get_state res') , Femto_VHDL_raw.add_to_beh2 (get_state res') (get_beh res') time def, def  \<turnstile> <nand4 , \<tau>_res
               (next_time time \<tau>_res := 0)> \<longrightarrow>\<^sub>c  \<tau>_res (next_time time \<tau>_res := 0)"
              using `disjnt {B, A} (next_event time \<tau>_res (get_state res'))` 
              unfolding nand4_def  by (simp add: b_conc_exec.intros(1))
            have " \<not> quiet (\<tau>_res(next_time time \<tau>_res := 0)) (next_event time \<tau>_res (get_state res'))"
              by (metis \<open>C \<in> next_event time \<tau>_res (get_state res')\<close> empty_iff quiet_def)
            have "(\<tau>_res (next_time time \<tau>_res := 0)) \<noteq> 0 \<Longrightarrow> Suc i \<le> next_time (next_time time \<tau>_res) (\<tau>_res (next_time time \<tau>_res := 0))"
              unfolding `next_time time \<tau>_res = time`
            proof (rule ccontr)
              assume " \<tau>_res(time := 0) \<noteq> 0"
              assume "\<not> Suc i \<le> next_time time (\<tau>_res (time := 0))"
              hence "next_time time (\<tau>_res (time := 0)) < Suc i"
                by auto
              have "to_trans_raw_sig (\<tau>_res (time := 0)) C = 0"
                using `\<And>n. n < time \<Longrightarrow> \<tau>_res n = 0`
                using `post_necessary_raw 0 (get_trans res') time C x' (get_state res' C)`
                unfolding to_trans_raw_sig_def \<tau>_res_def[THEN sym] trans_post_raw_def post_raw_def
                zero_fun_def zero_option_def 
                by (intro ext) auto
              have tr: "\<And>n. n < time \<Longrightarrow> (\<tau>_res (time := 0)) n = 0"
                using `\<And>n. n < time \<Longrightarrow> \<tau>_res n = 0` by auto
              have "time \<le> next_time time (\<tau>_res (time := 0))"
                by (intro next_time_at_least[OF tr] )
              moreover have "time \<noteq> next_time time (\<tau>_res (time := 0))"
                by (smt Suc_eq_plus1 Suc_n_not_le_n fun_upd_same less_Suc_eq next_time_at_least next_time_def tr)
              ultimately have "time < next_time time (\<tau>_res (time := 0))"
                by auto
              have "(\<tau>_res(time := 0)) (next_time time (\<tau>_res (time := 0))) \<noteq> 0"
                using `\<tau>_res (time := 0) \<noteq> 0` unfolding next_time_def zero_fun_def zero_option_def
              proof -
                assume a1: "\<tau>_res(time := Map.empty) \<noteq> (\<lambda>x. Map.empty)"
                have f2: "\<And>n. {s. (\<tau>_res(time := Map.empty)) n s \<noteq> None} = {} \<or> dom ((\<tau>_res(time := Map.empty)) (LEAST n. dom ((\<tau>_res(time := Map.empty)) n) \<noteq> {})) \<noteq> {}"
                  by (metis (mono_tags, lifting) LeastI_ex a1 dom_eq_empty_conv) 
                obtain nn :: nat and ss :: sig where f3: "(\<tau>_res(time := Map.empty)) nn ss \<noteq> None"
                  using a1 by meson
                obtain ssa :: "(sig \<Rightarrow> val option) \<Rightarrow> sig" where f4: "\<And>f s fa. (dom f \<noteq> {} \<or> f (s::sig) = (None::val option)) \<and> (fa (ssa fa) \<noteq> None \<or> dom fa = {})"
                  by (metis (no_types) dom_eq_empty_conv)
                then have "{s. (\<tau>_res(time := Map.empty)) (LEAST n. dom ((\<tau>_res(time := Map.empty)) n) \<noteq> {}) s \<noteq> None} \<noteq> {}"
                  using f3 f2 by (metis (no_types) dom_def)
                then have "{s. (\<tau>_res(time := Map.empty)) (if \<forall>n s. (\<tau>_res(time := Map.empty)) n s = None then Suc time else LEAST n. dom ((\<tau>_res(time := Map.empty)) n) \<noteq> {}) s \<noteq> None} = {} \<longrightarrow> (\<forall>n s. (\<tau>_res(time := Map.empty)) n s = None)"
                  by presburger
                then have "\<exists>s. (\<tau>_res(time := Map.empty)) (if \<forall>n s. (\<tau>_res(time := Map.empty)) n s = None then Suc time else LEAST n. dom ((\<tau>_res(time := Map.empty)) n) \<noteq> {}) s \<noteq> None"
                  using f4 f3 by blast
                then show "(\<tau>_res(time := Map.empty)) (if \<tau>_res(time := Map.empty) = (\<lambda>n. Map.empty) then time + 1 else LEAST n. dom ((\<tau>_res(time := Map.empty)) n) \<noteq> {}) \<noteq> Map.empty"
                  by (metis Suc_eq_plus1)
              qed
              hence "(\<tau>_res(time := 0)) (next_time time (\<tau>_res (time := 0))) B \<noteq> 0 \<or> 
                    (\<tau>_res(time := 0)) (next_time time (\<tau>_res (time := 0))) A \<noteq> 0" 
                using `to_trans_raw_sig (\<tau>_res (time := 0)) C = 0` unfolding to_trans_raw_sig_def
              proof -
                assume a1: "(\<lambda>n. (\<tau>_res(time := 0)) n C) = 0"
                obtain ss :: "sig set \<Rightarrow> sig set \<Rightarrow> sig" where
                  "\<forall>x0 x1. (\<exists>v2. v2 \<in> x1 \<and> v2 \<notin> x0) = (ss x0 x1 \<in> x1 \<and> ss x0 x1 \<notin> x0)"
                  by moura
                then have f2: "\<forall>S Sa. ss Sa S \<in> S \<and> ss Sa S \<notin> Sa \<or> S \<subseteq> Sa"
                  by (meson subsetI)
                then have "dom (0::sig \<Rightarrow> val option) \<subseteq> {}"
                  by (meson domIff zero_map)
                then have f3: "\<not> dom ((\<tau>_res(time := 0)) (next_time time (\<tau>_res(time := 0)))) \<subseteq> {}"
                  using \<open>(\<tau>_res(time := 0)) (next_time time (\<tau>_res(time := 0))) \<noteq> 0\<close> by auto
                have "(\<tau>_res(time := 0)) (next_time time (\<tau>_res(time := 0))) C = None"
                  using a1 by (metis (no_types) zero_map)
                then show ?thesis
                  using f3 f2 by (metis (full_types) domIff sig.exhaust zero_option_def)
              qed
              hence "get_trans res' (next_time time (\<tau>_res (time := 0))) B \<noteq> 0 \<or> 
                     get_trans res' (next_time time (\<tau>_res (time := 0))) A \<noteq> 0"
                using b_conc_exec_modifies_local_strongest[OF `time, get_state res', get_event res', get_beh res', def \<turnstile> <nand4, get_trans res'> \<longrightarrow>\<^sub>c \<tau>_res` `B \<notin> set (signals_from nand4)`]
                using b_conc_exec_modifies_local_strongest[OF `time, get_state res', get_event res', get_beh res', def \<turnstile> <nand4, get_trans res'> \<longrightarrow>\<^sub>c \<tau>_res` `B \<notin> set (signals_from nand4)`]
                using `time < next_time time (\<tau>_res (time := 0))` 
                using \<open>A \<notin> set (signals_from nand4)\<close> \<open>time , get_state res' , get_beh' res' , get_beh res', def \<turnstile> <nand4 , get_trans res'> \<longrightarrow>\<^sub>c \<tau>_res\<close> b_conc_exec_modifies_local_strongest by fastforce
              hence "(\<tau>'(t' := 0)) (next_time time (\<tau>_res(time := 0))) B \<noteq> None \<or> (\<tau>'(t' := 0)) (next_time time (\<tau>_res(time := 0))) A \<noteq> None"
                using b_simulate_fin_get_trans_gt_maxtime[OF bigstep2_pre `B \<notin> set (signals_from nand4)`]
                using b_simulate_fin_get_trans_gt_maxtime[OF bigstep2_pre `A \<notin> set (signals_from nand4)`]
                by (simp add: \<open>time < next_time time (\<tau>_res(time := 0))\<close> zero_option_def)
              hence "\<tau>' (next_time time (\<tau>_res(time := 0))) B \<noteq> None \<or> \<tau>' (next_time time (\<tau>_res(time := 0))) A \<noteq> None"
                by (metis fun_upd_other fun_upd_same zero_map)
              hence "\<tau> (next_time time (\<tau>_res(time := 0))) B \<noteq> None \<or> \<tau> (next_time time (\<tau>_res(time := 0))) A \<noteq> None"
                by (metis \<open>\<And>thesis. (\<And>x. \<lbrakk>0 , def , {} , 0, def \<turnstile> Bnand (Bsig A) (Bsig B) \<longrightarrow>\<^sub>b x;
                trans_post_raw C x (def C) \<tau> 0 0 = \<tau>'\<rbrakk> \<Longrightarrow> thesis) \<Longrightarrow> thesis\<close> sig.distinct(3)
                sig.distinct(5) to_trans_raw_sig_def trans_post_raw_diff_sig)
              thus "False"
                using inf_time_someE[OF \<open>inf_time (to_trans_raw_sig \<tau>) B i = Some time\<close>]
                \<open>time < next_time time (\<tau>_res(time:= 0))\<close> \<open>next_time time (\<tau>_res(time := 0)) < Suc i\<close>
                by (metis Suc_leI \<open>inf_time (to_trans_raw_sig \<tau>) A i = None\<close> domIff inf_time_noneE2 not_less_eq_eq to_trans_raw_sig_def zero_option_def)
            qed
            have "(\<tau>_res (next_time time \<tau>_res := 0)) = 0 \<Longrightarrow> next_time (next_time time \<tau>_res) (\<tau>_res (next_time time \<tau>_res := 0)) \<le> Suc i"
              unfolding `next_time time \<tau>_res = time` using `time < Suc i` by auto
            have "(\<tau>_res (next_time time \<tau>_res := 0)) = 0 \<or> (\<tau>_res (next_time time \<tau>_res := 0)) \<noteq> 0"
              by auto
            moreover
            { assume "(\<tau>_res (next_time time \<tau>_res := 0)) = 0"
              hence " next_time (next_time time \<tau>_res) (\<tau>_res (next_time time \<tau>_res := 0)) \<le> Suc i"
                using \<open>\<tau>_res(next_time time \<tau>_res := 0) = 0 \<Longrightarrow> next_time (next_time time \<tau>_res) (\<tau>_res(next_time time \<tau>_res := 0)) \<le> Suc i\<close> by blast
              hence bigstep4: " Suc i, next_time (next_time time \<tau>_res) (\<tau>_res (next_time time \<tau>_res := 0)) , 
                                       next_state (next_time time \<tau>_res) (\<tau>_res (next_time time \<tau>_res := 0)) (next_state time \<tau>_res (get_state res')) , 
                                       next_event (next_time time \<tau>_res) (\<tau>_res (next_time time \<tau>_res := 0)) (next_state time \<tau>_res (get_state res')) , 
                                       Femto_VHDL_raw.add_to_beh2 (next_state time \<tau>_res (get_state res')) (Femto_VHDL_raw.add_to_beh2 (get_state res') (get_beh res') time def) (next_time time \<tau>_res) def, def \<turnstile> 
                                        <nand4 , (\<tau>_res (next_time time \<tau>_res := 0)) (next_time (next_time time \<tau>_res) (\<tau>_res (next_time time \<tau>_res := 0)) := 0)> \<leadsto> res"
                using bau[OF bigstep3] `next_time time \<tau>_res < Suc i` 
                by (smt \<open>C \<in> next_event time \<tau>_res (get_state res')\<close> \<open>next_time time \<tau>_res , next_state time \<tau>_res (get_state res') , next_event time \<tau>_res (get_state res') , Femto_VHDL_raw.add_to_beh2 (get_state res') (get_beh res') time def, def \<turnstile> <nand4 , \<tau>_res (next_time time \<tau>_res := 0)> \<longrightarrow>\<^sub>c \<tau>_res (next_time time \<tau>_res := 0)\<close> bigstep3 case_bau empty_iff quiet_def)
              have "next_event (next_time time \<tau>_res) (\<tau>_res (next_time time \<tau>_res := 0)) (next_state time \<tau>_res (get_state res')) = {}"
                unfolding `(\<tau>_res (next_time time \<tau>_res := 0)) = 0` next_event_alt_def  next_state_def
                Let_def zero_fun_def zero_option_def 
                by (smt \<open>\<tau>_res(next_time time \<tau>_res := 0) = 0\<close> domIff empty_Collect_eq fun_upd_apply override_on_apply_notin zero_fun_def zero_map)
              have " (\<tau>_res (next_time time \<tau>_res := 0)) (next_time (next_time time \<tau>_res) (\<tau>_res (next_time time \<tau>_res := 0)) := 0) = 0"
                using `(\<tau>_res (next_time time \<tau>_res := 0)) = 0`  by (simp add: fun_upd_idem_iff zero_fun_def)
              have "next_time (next_time time \<tau>_res) (\<tau>_res (next_time time \<tau>_res := 0)) < Suc i \<or> next_time (next_time time \<tau>_res) (\<tau>_res (next_time time \<tau>_res := 0)) = Suc i"
                using \<open>next_time (next_time time \<tau>_res) (\<tau>_res(next_time time \<tau>_res := 0)) \<le> Suc i\<close> le_imp_less_or_eq by blast
              moreover
              { assume "next_time (next_time time \<tau>_res) (\<tau>_res (next_time time \<tau>_res := 0)) = Suc i"
                hence "res =
         (Suc i, next_state (next_time time \<tau>_res) (\<tau>_res(next_time time \<tau>_res := 0)) (next_state time \<tau>_res (get_state res')),
          next_event (next_time time \<tau>_res) (\<tau>_res(next_time time \<tau>_res := 0)) (next_state time \<tau>_res (get_state res')),
          Femto_VHDL_raw.add_to_beh2 (next_state time \<tau>_res (get_state res'))
           (Femto_VHDL_raw.add_to_beh2 (get_state res') (get_beh res') time def) (next_time time \<tau>_res) def,
          \<tau>_res(next_time time \<tau>_res := 0, next_time (next_time time \<tau>_res) (\<tau>_res(next_time time \<tau>_res := 0)) := 0))"
                  using bau[OF bigstep4] by auto
                hence gb_res: "get_beh res = Femto_VHDL_raw.add_to_beh2 (next_state time \<tau>_res (get_state res')) (Femto_VHDL_raw.add_to_beh2 (get_state res') (get_beh res') time def) (next_time time \<tau>_res) def"
                  by auto }
              moreover
              { assume "next_time (next_time time \<tau>_res) (\<tau>_res (next_time time \<tau>_res := 0)) < Suc i"
                hence "res =
         (Suc i, next_state (next_time time \<tau>_res) (\<tau>_res(next_time time \<tau>_res := 0)) (next_state time \<tau>_res (get_state res')),
          next_event (next_time time \<tau>_res) (\<tau>_res(next_time time \<tau>_res := 0)) (next_state time \<tau>_res (get_state res')),
          Femto_VHDL_raw.add_to_beh2 (next_state time \<tau>_res (get_state res'))
           (Femto_VHDL_raw.add_to_beh2 (get_state res') (get_beh res') time def) (next_time time \<tau>_res) def,
          0)"
                  using bau[OF bigstep4] 
                  by (smt \<open>\<tau>_res (next_time time \<tau>_res := 0, next_time (next_time time \<tau>_res)
                  (\<tau>_res(next_time time \<tau>_res := 0)) := 0) = 0\<close> \<open>next_event (next_time time \<tau>_res)
                  (\<tau>_res(next_time time \<tau>_res := 0)) (next_state time \<tau>_res (get_state res')) = {}\<close>
                  quiet_def)
                hence "get_beh res = Femto_VHDL_raw.add_to_beh2 (next_state time \<tau>_res (get_state res'))
           (Femto_VHDL_raw.add_to_beh2 (get_state res') (get_beh res') time def) (next_time time \<tau>_res) def"
                  by auto }
              ultimately have gb_res: "get_beh res = Femto_VHDL_raw.add_to_beh2 (next_state time \<tau>_res (get_state res')) (Femto_VHDL_raw.add_to_beh2 (get_state res') (get_beh res') time def) (next_time time \<tau>_res) def"
                by auto
              have " (next_time time \<tau>_res) \<le> i"
                using \<open>next_time time \<tau>_res < Suc i\<close> less_Suc_eq_le by blast
              have "signal_of (def C) (get_beh res) C i = (next_state time \<tau>_res (get_state res')) C"
                unfolding gb_res
                apply (intro signal_of_add_to_beh2'[OF `next_time time \<tau>_res \<le> i`] )
                by (smt Femto_VHDL_raw.add_to_beh2_def \<open>next_time time \<tau>_res = time\<close> b_simulate_fin_preserves_hist bigstep2_pre fun_upd_other nat_neq_iff trans_removal zero_fun_def)
              also have "... = the (\<tau>_res time C)"
                unfolding next_state_def `next_time time \<tau>_res = time` Let_def 
                by (metis \<open>\<tau>_res time C \<noteq> 0\<close> comp_apply domIff override_on_apply_in zero_option_def)
              also have "... = x'"
                by (simp add: \<open>\<tau>_res time C = Some x'\<close>)
              finally have "signal_of (def C) (get_beh res) C i = x'"
                by auto
              have "signal_of (def B) \<tau> B i  = signal_of (def B) \<tau>' B i"
                using init'_modifies_local_strongest[OF `init' 0 def {} 0 def nand4 \<tau> \<tau>'` `B \<notin> set (signals_from nand4)`]
                using \<open>trans_post_raw C x (def C) \<tau> 0 0 = \<tau>'\<close> signal_of_trans_post by fastforce
              also have "... = signal_of (\<sigma>' B) \<tau>' B i"
                by (metis \<open>inf_time (to_trans_raw_sig \<tau>) B i = Some time\<close> \<open>trans_post_raw C x (def C) \<tau> 0 0 = \<tau>'\<close> comp_apply option.simps(5) sig.distinct(5) signal_of_trans_post to_signal_def)
              also have "... = signal_of (\<sigma>' B) (\<tau>'(t':=0)) B i"
                by (smt \<open>next_state 0 \<tau>' def = \<sigma>'\<close> \<open>next_time 0 \<tau>' = t'\<close> comp_apply next_state_def next_time_at_least2 override_on_apply_in signal_of_rem_curr_trans_at_t)
              also have "... = signal_of (get_state res' B) (get_trans res') B i"
                using bau_signal_of[OF bigstep2_pre `B \<notin> set (signals_from nand4)` _ trans_removal] `time < Suc i`
                using less_Suc_eq_le by blast
              also have "... = get_state res' B"
                by (metis (mono_tags, lifting) \<open>B \<notin> set (signals_from nand4)\<close> \<open>\<tau>_res time B = 0\<close>
                \<open>\<tau>_res(next_time time \<tau>_res := 0) = 0\<close> \<open>next_time time \<tau>_res = time\<close> \<open>time , get_state
                res' , get_beh' res' , get_beh res', def \<turnstile> <nand4 , get_trans res'> \<longrightarrow>\<^sub>c \<tau>_res\<close>
                b_conc_exec_modifies_local_strongest fun_upd_def signal_of_def zero_fun_def)
              finally have "signal_of (def B) \<tau> B i = get_state res' B"
                by auto
              have "signal_of (def A) \<tau> A i  = def A"
                using `inf_time (to_trans_raw_sig \<tau>) A i = None` 
                by (simp add: to_signal_def)
              also have "... = \<sigma>' A"
              proof -
                have "A \<notin> (dom (\<tau>' (next_time 0 \<tau>')))"
                  using \<open>inf_time (to_trans_raw_sig \<tau>) A i = None\<close>
                  using init'_modifies_local_strongest[OF `init' 0 def {} 0 def nand4 \<tau> \<tau>'` `A \<notin> set (signals_from nand4)`]          
                  by (metis \<open>next_time 0 \<tau>' \<le> time\<close> \<open>next_time time \<tau>_res = time\<close> \<open>next_time time \<tau>_res \<le> i\<close> domD domI inf_time_none_iff leD le_trans to_trans_raw_sig_def)
                thus ?thesis
                  unfolding `next_state 0 \<tau>' def = \<sigma>'`[THEN sym] next_state_def Let_def  by simp
              qed
              also have "... = get_state res' A"
              proof -
                have "inf_time (to_trans_raw_sig (\<tau>'(t' := 0))) A time = None"
                  unfolding inf_time_none_iff[THEN sym]
                proof 
                  { fix x 
                    assume " x \<in> dom (to_trans_raw_sig (\<tau>'(t' := 0)) A)"
                    hence "(\<tau>'(t' := 0)) x A \<noteq> None"
                      unfolding dom_def to_trans_raw_sig_def by auto
                    hence "x \<noteq> t'"
                      unfolding fun_upd_def zero_fun_def zero_option_def by auto
                    assume "x \<le> time"
                    have "(\<tau>'(t' := 0)) x A = \<tau>' x A"
                      using `x \<noteq> t'` by auto
                    also have "... = \<tau> x A"
                      using init'_modifies_local_strongest[OF `init' 0 def {} 0 def nand4 \<tau> \<tau>'` `A \<notin> set (signals_from nand4)`]          
                      by auto
                    also have "... = None"
                      using \<open>inf_time (to_trans_raw_sig \<tau>) A i = None\<close> 
                      by (metis \<open>inf_time (to_trans_raw_sig \<tau>) B i = Some time\<close> \<open>x \<le> time\<close> inf_time_at_most inf_time_noneE2 le_trans to_trans_raw_sig_def zero_option_def) 
                    finally have "False"
                      using \<open>(\<tau>'(t' := 0)) x A \<noteq> None\<close> by blast }
                  thus "\<And>x. x \<in> dom (to_trans_raw_sig (\<tau>'(t' := 0)) A) \<Longrightarrow> time < x"
                    using le_less_linear by blast
                qed
                thus ?thesis
                  using get_state_b_simulate_fin_inf_none[OF bigstep2_pre `A \<notin> set (signals_from nand4)`] 
                  by auto
              qed
              finally have "signal_of (def A) \<tau> A i = get_state res' A"
                by auto
              have "time , get_state res' , get_beh' res' , get_beh res', def  \<turnstile> Bsig B \<longrightarrow>\<^sub>b Bv (bval_of (get_state res' B))"
                by (smt \<open>0 , def , {} , 0, def \<turnstile> Bnand (Bsig A) (Bsig B) \<longrightarrow>\<^sub>b x\<close> \<open>signal_of (def B) \<tau> B i =
                get_state res' B\<close> \<open>x = Bv (\<not> (bval_of (def A) \<and> bval_of (def B)))\<close> assms(4) assms(6)
                beval_cases(1) beval_cases(9) beval_raw.intros(1) signal_of_preserve_well_typedness
                styping_def ty.simps(3) type_of.simps(1) type_of.simps(2) val.exhaust_sel)
              moreover have "time , get_state res' , get_beh' res' , get_beh res', def  \<turnstile> Bsig A \<longrightarrow>\<^sub>b Bv (bval_of (get_state res' A))"
                by (smt \<open>time , get_state res' , get_beh' res' , get_beh res', def \<turnstile> Bnand (Bsig A) (Bsig B)
                \<longrightarrow>\<^sub>b x'\<close> \<open>time , get_state res' , get_beh' res' , get_beh res', def \<turnstile> Bsig B \<longrightarrow>\<^sub>b Bv (bval_of
                (get_state res' B))\<close> beval_cases(9) beval_raw.intros(1) beval_raw_deterministic
                val.distinct(1) val.exhaust_sel)
              ultimately have "x' = Bv (\<not> (bval_of (get_state res' B) \<and> bval_of (get_state res' A)))"
                using beval_cases(9)[OF `time , get_state res' , get_beh' res' , get_beh res', def  \<turnstile> Bnand (Bsig A) (Bsig B) \<longrightarrow>\<^sub>b x'`]
                by (smt beval_cases(1) val.distinct(1))
              hence ?thesis
                using \<open>signal_of (def B) \<tau> B i = get_state res' B\<close> \<open>signal_of (def A) \<tau> A i = get_state res' A\<close> \<open>signal_of (def C) (get_beh res) C i = x'\<close> 
                by auto }
            moreover
            { assume " (\<tau>_res (next_time time \<tau>_res := 0)) \<noteq> 0"
              hence "Suc i \<le> next_time (next_time time \<tau>_res) (\<tau>_res (next_time time \<tau>_res := 0))"
                using \<open>\<tau>_res(next_time time \<tau>_res := 0) \<noteq> 0 \<Longrightarrow> Suc i \<le> next_time (next_time time \<tau>_res)
                (\<tau>_res(next_time time \<tau>_res := 0))\<close> by metis
              hence "Suc i < next_time (next_time time \<tau>_res) (\<tau>_res (next_time time \<tau>_res := 0)) \<or> Suc i = next_time (next_time time \<tau>_res) (\<tau>_res (next_time time \<tau>_res := 0))"        
                by auto
              moreover
              { assume "Suc i = next_time (next_time time \<tau>_res) (\<tau>_res (next_time time \<tau>_res := 0))"
                hence bigstep4: " Suc i, next_time (next_time time \<tau>_res) (\<tau>_res (next_time time \<tau>_res := 0)) , 
                                         next_state (next_time time \<tau>_res) (\<tau>_res (next_time time \<tau>_res := 0)) (next_state time \<tau>_res (get_state res')) , 
                                         next_event (next_time time \<tau>_res) (\<tau>_res (next_time time \<tau>_res := 0)) (next_state time \<tau>_res (get_state res')) , 
                                         Femto_VHDL_raw.add_to_beh2 (next_state time \<tau>_res (get_state res')) (Femto_VHDL_raw.add_to_beh2 (get_state res') (get_beh res') time def) (next_time time \<tau>_res) def, def \<turnstile> 
                                          <nand4 , (\<tau>_res (next_time time \<tau>_res := 0)) (next_time (next_time time \<tau>_res) (\<tau>_res (next_time time \<tau>_res := 0)) := 0)> \<leadsto> res"
                  using bau[OF bigstep3] `next_time time \<tau>_res < Suc i` 
                  by (smt \<open>Suc i \<le> next_time (next_time time \<tau>_res) (\<tau>_res(next_time time \<tau>_res := 0))\<close> \<open>\<tau>_res(next_time time \<tau>_res := 0) \<noteq> 0\<close> \<open>next_time time \<tau>_res , next_state time \<tau>_res (get_state res') , next_event time \<tau>_res (get_state res') , Femto_VHDL_raw.add_to_beh2 (get_state res') (get_beh res') time def, def \<turnstile> <nand4 , \<tau>_res (next_time time \<tau>_res := 0)> \<longrightarrow>\<^sub>c \<tau>_res (next_time time \<tau>_res := 0)\<close> bigstep3 case_bau quiet_def)
                hence "res =
         (Suc i, next_state (next_time time \<tau>_res) (\<tau>_res(next_time time \<tau>_res := 0)) (next_state time \<tau>_res (get_state res')),
          next_event (next_time time \<tau>_res) (\<tau>_res(next_time time \<tau>_res := 0)) (next_state time \<tau>_res (get_state res')),
          Femto_VHDL_raw.add_to_beh2 (next_state time \<tau>_res (get_state res'))
           (Femto_VHDL_raw.add_to_beh2 (get_state res') (get_beh res') time def) (next_time time \<tau>_res) def,
          \<tau>_res(next_time time \<tau>_res := 0, next_time (next_time time \<tau>_res) (\<tau>_res(next_time time \<tau>_res := 0)) := 0))"
                  using bau[OF bigstep4] 
                  using \<open>Suc i = next_time (next_time time \<tau>_res) (\<tau>_res(next_time time \<tau>_res := 0))\<close> by fastforce
                hence "get_beh res = Femto_VHDL_raw.add_to_beh2 (next_state time \<tau>_res (get_state res')) (Femto_VHDL_raw.add_to_beh2 (get_state res') (get_beh res') time def) (next_time time \<tau>_res) def"
                  by auto }
              moreover
              { assume "Suc i < next_time (next_time time \<tau>_res) (\<tau>_res (next_time time \<tau>_res := 0))"
                hence "res =
               (Suc i, next_state time \<tau>_res (get_state res'), {},
                Femto_VHDL_raw.add_to_beh2 (next_state time \<tau>_res (get_state res'))
                 (Femto_VHDL_raw.add_to_beh2 (get_state res') (get_beh res') time def) (next_time time \<tau>_res) def, \<tau>_res (next_time time \<tau>_res := 0))"
                  using bau[OF bigstep3] `next_time time \<tau>_res < Suc i` \<open> \<not> quiet (\<tau>_res(next_time time \<tau>_res := 0)) (next_event time \<tau>_res (get_state res'))\<close>
                  \<open>next_time time
                \<tau>_res , next_state time \<tau>_res
                         (get_state res') , next_event time \<tau>_res (get_state res') , Femto_VHDL_raw.add_to_beh2 (get_state res') (get_beh res') time def, def  \<turnstile> <nand4 , \<tau>_res
               (next_time time \<tau>_res := 0)> \<longrightarrow>\<^sub>c  \<tau>_res (next_time time \<tau>_res := 0)\<close> 
                  by (smt b_conc_exec_deterministic less_le_not_le)
                hence "get_beh res = Femto_VHDL_raw.add_to_beh2 (next_state time \<tau>_res (get_state res')) (Femto_VHDL_raw.add_to_beh2 (get_state res') (get_beh res') time def) (next_time time \<tau>_res) def"
                  by auto }
              ultimately have gb_res: "get_beh res = Femto_VHDL_raw.add_to_beh2 (next_state time \<tau>_res (get_state res')) (Femto_VHDL_raw.add_to_beh2 (get_state res') (get_beh res') time def) (next_time time \<tau>_res) def"
                  by auto
              have " (next_time time \<tau>_res) \<le> i"
                using \<open>next_time time \<tau>_res < Suc i\<close> less_Suc_eq_le by blast
              have "signal_of (def C) (get_beh res) C i = (next_state time \<tau>_res (get_state res')) C"
                unfolding gb_res
                apply (intro signal_of_add_to_beh2'[OF `next_time time \<tau>_res \<le> i`] )
                by (smt Femto_VHDL_raw.add_to_beh2_def \<open>next_time time \<tau>_res = time\<close> b_simulate_fin_preserves_hist bigstep2_pre fun_upd_other nat_neq_iff trans_removal zero_fun_def)
              also have "... = the (\<tau>_res time C)"
                unfolding next_state_def `next_time time \<tau>_res = time` Let_def 
                by (metis \<open>\<tau>_res time C \<noteq> 0\<close> comp_apply domIff override_on_apply_in zero_option_def)
              also have "... = x'"
                by (simp add: \<open>\<tau>_res time C = Some x'\<close>)
              finally have "signal_of (def C) (get_beh res) C i = x'"
                by auto
              have "signal_of (def B) \<tau> B i  = signal_of (def B) \<tau>' B i"
                using init'_modifies_local_strongest[OF `init' 0 def {} 0 def nand4 \<tau> \<tau>'` `B \<notin> set (signals_from nand4)`]
                using \<open>trans_post_raw C x (def C) \<tau> 0 0 = \<tau>'\<close> signal_of_trans_post by fastforce
              also have "... = signal_of (\<sigma>' B) \<tau>' B i"
                by (metis \<open>inf_time (to_trans_raw_sig \<tau>) B i = Some time\<close> \<tau>'_def comp_def option.simps(5) sig.simps(6) signal_of_trans_post to_signal_def)
              also have "... = signal_of (\<sigma>' B) (\<tau>'(t':=0)) B i"
                by (smt \<open>next_state 0 \<tau>' def = \<sigma>'\<close> \<open>next_time 0 \<tau>' = t'\<close> comp_apply next_state_def next_time_at_least2 override_on_apply_in signal_of_rem_curr_trans_at_t)
              also have "... = signal_of (get_state res' B) (get_trans res') B i"
                using bau_signal_of[OF bigstep2_pre `B \<notin> set (signals_from nand4)` _ trans_removal] `time < Suc i`
                using less_Suc_eq_le by blast
              also have "... = get_state res' B"
                by (smt \<open>B \<notin> set (signals_from nand4)\<close> \<open>Suc i \<le> next_time (next_time time \<tau>_res)
                (\<tau>_res(next_time time \<tau>_res := 0))\<close> \<open>\<tau>_res time B = 0\<close> \<open>get_trans res' time = 0\<close>
                \<open>next_time time \<tau>_res = time\<close> \<open>time , get_state res' , get_beh' res' , get_beh res', def
                \<turnstile> <nand4 , get_trans res'> \<longrightarrow>\<^sub>c \<tau>_res\<close> antisym_conv2 b_conc_exec_modifies_local_strongest
                dual_order.strict_trans2 fun_upd_other lessI next_time_at_least2 signal_of_def
                signal_of_suc_sig)
              finally have "signal_of (def B) \<tau> B i = get_state res' B"
                by auto
              have "signal_of (def A) \<tau> A i  = def A"
                using `inf_time (to_trans_raw_sig \<tau>) A i = None` 
                by (simp add: to_signal_def)
              also have "... = \<sigma>' A"
              proof -
                have "A \<notin> (dom (\<tau>' (next_time 0 \<tau>')))"
                  using \<open>inf_time (to_trans_raw_sig \<tau>) A i = None\<close>
                  using init'_modifies_local_strongest[OF `init' 0 def {} 0 def nand4 \<tau> \<tau>'` `A \<notin> set (signals_from nand4)`]          
                  by (metis \<open>next_time 0 \<tau>' \<le> time\<close> \<open>next_time time \<tau>_res = time\<close> \<open>next_time time
                  \<tau>_res \<le> i\<close> domD domI inf_time_none_iff leD order.trans to_trans_raw_sig_def)
                thus ?thesis
                  unfolding `next_state 0 \<tau>' def = \<sigma>'`[THEN sym] next_state_def Let_def  by simp
              qed
              also have "... = get_state res' A"
              proof -
                have "inf_time (to_trans_raw_sig (\<tau>'(t' := 0))) A time = None"
                  unfolding inf_time_none_iff[THEN sym]
                proof 
                  { fix x 
                    assume " x \<in> dom (to_trans_raw_sig (\<tau>'(t' := 0)) A)"
                    hence "(\<tau>'(t' := 0)) x A \<noteq> None"
                      unfolding dom_def to_trans_raw_sig_def by auto
                    hence "x \<noteq> t'"
                      unfolding fun_upd_def zero_fun_def zero_option_def by auto
                    assume "x \<le> time"
                    have "(\<tau>'(t' := 0)) x A = \<tau>' x A"
                      using `x \<noteq> t'` by auto
                    also have "... = \<tau> x A"
                      using init'_modifies_local_strongest[OF `init' 0 def {} 0 def nand4 \<tau> \<tau>'` `A \<notin> set (signals_from nand4)`]          
                      by auto
                    also have "... = None"
                      using \<open>inf_time (to_trans_raw_sig \<tau>) A i = None\<close> \<open>time < Suc i\<close> 
                      by (metis \<open>next_time time \<tau>_res = time\<close> \<open>next_time time \<tau>_res \<le> i\<close> \<open>x \<le> time\<close>
                      inf_time_noneE2 le_trans to_trans_raw_sig_def zero_option_def)
                    finally have "False"
                      using \<open>(\<tau>'(t' := 0)) x A \<noteq> None\<close> by blast }
                  thus "\<And>x. x \<in> dom (to_trans_raw_sig (\<tau>'(t' := 0)) A) \<Longrightarrow> time < x"
                    using le_less_linear by blast
                qed
                thus ?thesis
                  using get_state_b_simulate_fin_inf_none[OF bigstep2_pre `A \<notin> set (signals_from nand4)`] 
                  by auto
              qed
              finally have "signal_of (def A) \<tau> A i = get_state res' A"
                by auto
              have "time , get_state res' , get_beh' res' , get_beh res', def  \<turnstile> Bsig B \<longrightarrow>\<^sub>b Bv (bval_of (get_state res' B))"
                by (smt \<open>0 , def , {} , 0, def \<turnstile> Bnand (Bsig A) (Bsig B) \<longrightarrow>\<^sub>b x\<close> \<open>signal_of (def B) \<tau> B i =
                get_state res' B\<close> \<open>x = Bv (\<not> (bval_of (def A) \<and> bval_of (def B)))\<close> assms(4) assms(6)
                beval_cases(1) beval_cases(9) beval_raw.intros(1) signal_of_preserve_well_typedness
                styping_def ty.simps(3) type_of.simps(1) type_of.simps(2) val.exhaust_sel)
              moreover have "time , get_state res' , get_beh' res' , get_beh res', def  \<turnstile> Bsig A \<longrightarrow>\<^sub>b Bv (bval_of (get_state res' A))"
                by (smt \<open>time , get_state res' , get_beh' res' , get_beh res', def \<turnstile> Bnand (Bsig A) (Bsig B)
                \<longrightarrow>\<^sub>b x'\<close> \<open>time , get_state res' , get_beh' res' , get_beh res', def \<turnstile> Bsig B \<longrightarrow>\<^sub>b Bv (bval_of
                (get_state res' B))\<close> beval_cases(9) beval_raw.intros(1) beval_raw_deterministic
                val.distinct(1) val.exhaust_sel)
              ultimately have "x' = Bv (\<not> (bval_of (get_state res' B) \<and> bval_of (get_state res' A)))"
                using beval_cases(9)[OF `time , get_state res' , get_beh' res' , get_beh res', def  \<turnstile> Bnand (Bsig A) (Bsig B) \<longrightarrow>\<^sub>b x'`]
                by (smt beval_cases(1) val.distinct(1))
              hence ?thesis
                using \<open>signal_of (def B) \<tau> B i = get_state res' B\<close> \<open>signal_of (def A) \<tau> A i = get_state res' A\<close> \<open>signal_of (def C) (get_beh res) C i = x'\<close> 
                by auto }
            ultimately have ?thesis
              by auto }
          ultimately have ?thesis
            by auto }
        ultimately have ?thesis
          using nat_neq_iff by blast }
    ultimately show ?thesis
      by auto
  qed
qed

lemma signal_of2_cong_neq_none_at_0:
  assumes " (to_trans_raw_sig \<tau> sig) 0 \<noteq> None"
  shows "signal_of def1 \<tau> sig i = signal_of def2 \<tau> sig i"
proof -
  have "inf_time (to_trans_raw_sig \<tau>) sig i \<noteq> None"
  proof (rule ccontr)
    assume "\<not> inf_time (to_trans_raw_sig \<tau>) sig i \<noteq> None"
    hence "inf_time (to_trans_raw_sig \<tau>) sig i = None"
      by auto
    hence "\<forall>k. k \<le> i \<longrightarrow>  (to_trans_raw_sig \<tau> sig) k = 0"
      by (auto dest!: inf_time_noneE2)
    hence " (to_trans_raw_sig \<tau> sig) 0 = 0"
      by auto
    with assms show "False"
      by (simp add: zero_option_def)
  qed
  thus ?thesis
    unfolding to_signal_def comp_def by auto
qed

end