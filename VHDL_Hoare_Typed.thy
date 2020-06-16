(*
 * Copyright 2019, NTU
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 *  Author: Albert Rizaldi, NTU Singapore
 *)

theory VHDL_Hoare_Typed
  imports VHDL_Hoare_Complete 
begin

term "wityping"

definition
seq_hoare_valid2_wt :: "'signal tyenv \<Rightarrow> 'signal assn2 \<Rightarrow> 'signal seq_stmt \<Rightarrow> 'signal assn2 \<Rightarrow> bool" ("(1_) \<Turnstile> [(1_)]/ (_)/ [(1_)]" 50)
where "\<Gamma> \<Turnstile> [P] s [Q] \<longleftrightarrow>  (\<forall>tw tw'.  wityping \<Gamma> (snd tw) \<and> P tw \<and> (tw, s \<Rightarrow>\<^sub>s tw') \<longrightarrow> Q tw')"

fun eval_logical :: "val \<Rightarrow> val \<Rightarrow> (bool \<Rightarrow> bool \<Rightarrow> bool) \<Rightarrow> val" where
  "eval_logical v1 v2 ope  = (case (v1, v2) of 
                                    (Bv val1   , Bv val2   ) \<Rightarrow> Bv (ope val1 val2)
                                  | (Lv ki1 bs1, Lv ki2 bs2) \<Rightarrow> Lv ki1 (map2 ope bs1 bs2))"

fun eval_arith   :: "val \<Rightarrow> val \<Rightarrow> (nat \<Rightarrow> nat \<Rightarrow> nat) \<Rightarrow> (int \<Rightarrow> int \<Rightarrow> int) \<Rightarrow> val" where
  "eval_arith v1 v2 ope1 ope2 = (case (v1, v2) of 
                                     (Lv Uns bs1, Lv Uns bs2) \<Rightarrow> (let len = ope1 (length bs1) (length bs2); 
                                                                      res = bin_to_bl len (ope2 (bl_to_bin bs1) (bl_to_bin bs2)) 
                                                                  in 
                                                                      Lv Uns res)
                                   | (Lv Sig bs1, Lv Sig bs2) \<Rightarrow> (let len = ope1 (length bs1) (length bs2); 
                                                                      res = bin_to_bl len (ope2 (sbl_to_bin bs1) (sbl_to_bin bs2)) 
                                                                  in 
                                                                      Lv Sig res))"  

function eval_world_raw :: "nat \<Rightarrow> 'signal worldline_init \<Rightarrow> 'signal bexp \<Rightarrow> val" where

  "eval_world_raw t w (Band e1 e2)        = eval_logical (eval_world_raw t w e1) (eval_world_raw t w e2) (\<and>)"
| "eval_world_raw t w (Bor e1 e2)         = eval_logical (eval_world_raw t w e1) (eval_world_raw t w e2) (\<or>)"
| "eval_world_raw t w (Bnand e1 e2)       = eval_logical (eval_world_raw t w e1) (eval_world_raw t w e2) (\<lambda>x y. \<not> (x \<and> y))"
| "eval_world_raw t w (Bnor  e1 e2)       = eval_logical (eval_world_raw t w e1) (eval_world_raw t w e2) (\<lambda>x y. \<not> (x \<or> y))"
| "eval_world_raw t w (Bxor  e1 e2)       = eval_logical (eval_world_raw t w e1) (eval_world_raw t w e2) xor"
| "eval_world_raw t w (Bxnor  e1 e2)      = eval_logical (eval_world_raw t w e1) (eval_world_raw t w e2) (\<lambda>x y. \<not> xor x y)" 

| "eval_world_raw t w (Badd e1 e2)        = eval_arith (eval_world_raw t w e1) (eval_world_raw t w e2) max (+)"
| "eval_world_raw t w (Bmult e1 e2)       = eval_arith (eval_world_raw t w e1) (eval_world_raw t w e2) (+) (*)"
| "eval_world_raw t w (Bsub e1 e2)        = eval_arith (eval_world_raw t w e1) (eval_world_raw t w e2) max (-)"

| "eval_world_raw t w (Bsig sig)          = snd w sig t"
| "eval_world_raw t w (Btrue)             = Bv True"
| "eval_world_raw t w (Bfalse)            = Bv False"               
| "eval_world_raw t w (Bsig_delayed sig dly) = (if t - dly < t then snd w sig (t - dly) else if 0 < t then snd w sig (t - 1) else fst w sig)"
| "eval_world_raw t w (Bsig_event sig)    = Bv (sig \<in> event_of (t, w))"
| "eval_world_raw t w (Bnot e)            = (case eval_world_raw t w e of 
                                                    Bv bool   \<Rightarrow> Bv (\<not> bool)
                                                  | Lv ki bs  \<Rightarrow> Lv ki (map Not bs))"

| "eval_world_raw t w (Bslice sig l r)    = (case eval_world_raw t w (Bsig sig) of 
                                                   Lv ki bs \<Rightarrow>  Lv ki (nths bs {length bs - l - 1 .. length bs - r - 1}))"

| "eval_world_raw t w (Bindex sig idx)    = (case eval_world_raw t w (Bsig sig) of 
                                                   Lv ki bs \<Rightarrow>  Bv (bs ! idx))"


| "eval_world_raw t w (Bshiftl e n)       = (case eval_world_raw t w e of 
                                                    Lv Uns bs  \<Rightarrow> Lv Uns (drop n (bs @ replicate n False))
                                                  | Lv Sig bs  \<Rightarrow> Lv Sig (drop n (bs @ replicate n False)))"

| "eval_world_raw t w (Bshiftr e n)       = (case eval_world_raw t w e of 
                                                    Lv Uns bs \<Rightarrow> Lv Uns (take (length bs) (replicate n False   @ bs))
                                                  | Lv Sig bs \<Rightarrow> Lv Sig (take (length bs) (replicate n (hd bs) @ bs)))"

| "eval_world_raw t w (Bwhen th guard el) = (case eval_world_raw t w guard of 
                                                    Bv True  \<Rightarrow> eval_world_raw t w th 
                                                  | Bv False \<Rightarrow> eval_world_raw t w el)"

| "eval_world_raw t w (Bliteral sign val) = (Lv sign val)"
  by pat_completeness auto

termination
  by size_change

lemma eval_world_raw_bv: 
  assumes "bexp_wt \<Gamma> exp Bty" and "wityping \<Gamma> w"
  shows   "\<exists>v. eval_world_raw t w exp = Bv v"
  using assms
proof (induction rule:eval_world_raw.induct)
  case (1 t w e1 e2)
  show ?case
    apply (rule bexp_wt.cases[OF 1(3)])
    using 1 by auto
next
  case (2 t w e1 e2)
  show ?case 
    apply (rule bexp_wt.cases[OF 2(3)])
    using 2 by auto
next
  case (3 t w e1 e2)
  show ?case 
    apply (rule bexp_wt.cases[OF 3(3)])
    using 3 by auto
next
  case (4 t w e1 e2)
  show ?case 
    apply (rule bexp_wt.cases[OF 4(3)])
    using 4 by auto
next
  case (5 t w e1 e2)
  show ?case 
    apply (rule bexp_wt.cases[OF 5(3)])
    using 5 by auto
next
  case (6 t w e1 e2)
  show ?case 
    apply (rule bexp_wt.cases[OF 6(3)])
    using 6  by auto
next
  case (7 t w e1 e2)
  show ?case 
    apply (rule bexp_wt.cases[OF 7(3)])
    using 7 by auto
next
  case (8 t w e1 e2)
  show ?case 
    apply (rule bexp_wt.cases[OF 8(3)])
    using 8 by auto
next
  case (9 t w e1 e2)
  show ?case 
    by (rule bexp_wt.cases[OF 9(3)]) auto
next
  case (10 t w sig)
  show ?case
    apply (rule bexp_wt_cases_slice(2)[OF 10(1)])
    using 10 
    by (metis (no_types, hide_lams) eval_world_raw.simps(10) ty.distinct(1) type_of.elims wityping_def wtyping_def)
next
  case (11 t w)
  then show ?case by auto
next
  case (12 t w)
  then show ?case by auto
next
  case (13 t w sig dly)
  show ?case 
    apply (rule bexp_wt_cases_del[OF 13(1)])
    using 13 unfolding wityping_def wtyping_def 
    by (metis (full_types) eval_world_raw.simps(13) styping_def ty.distinct(1) type_of.elims)
next
  case (14 t w sig)
  show ?case  by auto
next
  case (15 t w e)
  hence *: "\<exists>v. eval_world_raw t w e = Bv v"
    using bexp_wt_cases(1) by blast
  show ?case 
    apply (rule bexp_wt_cases(1)[OF 15(2)])
    using 15 * by auto
next
  case (16 t w sig l r)
  then show ?case 
    by (meson bexp_wt_cases_slice(1) ty.distinct(1))
next
  case (17 t w sig idx)
  then show ?case 
    by (metis (no_types, lifting) bexp_wt_cases_slice(3) bexp_wt_cases_slice(2) eval_world_raw.simps(10)
    eval_world_raw.simps(17) is_Bv_def ty.simps(3) type_of.simps(1) val.case_eq_if wityping_def
    wtyping_def)
next
  case (18 t w e n)
  then show ?case 
    by (meson bexp_wt_cases_shiftl ty.distinct(1))
next
  case (19 t w e n)
  then show ?case 
    by (meson bexp_wt_cases_shiftr ty.distinct(1))
next
  case (20 t w th guard el)
  hence *: "\<exists>v. eval_world_raw t w guard = Bv v"
    using bexp_wt_cases_when by blast
  show ?case 
    apply (rule bexp_wt_cases_when[OF 20(4)])
    using * 20  by (smt eval_world_raw.simps(20) val.simps(5))
next
  case (21 t w sign val)
  then show ?case 
    using bexp_wt_cases_lit by blast
qed  

lemma bexp_wt_add:
  assumes "bexp_wt \<Gamma> (Badd e1 e2) (Lty ki len)"
  shows   "\<exists>len1 len2. bexp_wt \<Gamma> e1 (Lty ki len1) \<and> bexp_wt \<Gamma> e2 (Lty ki len2) \<and> len = max len1 len2 \<and> (ki = Uns \<or> ki = Sig)"
  by (rule bexp_wt_cases_add[OF assms]) blast+

lemma bexp_wt_mult:
  assumes "bexp_wt \<Gamma> (Bmult e1 e2) (Lty ki len)"
  shows   "\<exists>len1 len2. bexp_wt \<Gamma> e1 (Lty ki len1) \<and> bexp_wt \<Gamma> e2 (Lty ki len2) \<and> len =  len1 + len2 \<and> (ki = Uns \<or> ki = Sig)"
  by (rule bexp_wt_cases_mult[OF assms]) blast+

lemma bexp_wt_sub:
  assumes "bexp_wt \<Gamma> (Bsub e1 e2) (Lty ki len)"
  shows   "\<exists>len1 len2. bexp_wt \<Gamma> e1 (Lty ki len1) \<and> bexp_wt \<Gamma> e2 (Lty ki len2) \<and> len = max len1 len2 \<and> (ki = Uns \<or> ki = Sig)"
  by (rule bexp_wt_cases_sub[OF assms]) blast+

lemma card_slice:
  assumes "l < len" and "r \<le> l"
  shows "card {i. i < len \<and> i \<in> {len - Suc l..len - Suc r}} = Suc (l - r)" (is "card ?lhs = _")
  using assms
proof -
  have "\<forall>i \<in> {len - Suc l .. len - Suc r}. i < len"
  proof (rule)
    fix i
    assume "i \<in> {len - Suc l .. len - Suc r}"
    hence "len - Suc l \<le> i" and "i \<le> len - Suc r"
      by auto
    thus "i < len"
      using assms by linarith
  qed
  hence "{len - Suc l .. len - Suc r} \<subseteq> {i. i < len}"
    by auto
  have "?lhs = ({len - Suc l .. len - Suc r})"
    using assms by auto
  hence "card ?lhs = card {len - Suc l .. len - Suc r}"
    by auto
  also have "... = Suc (l - r)"
    unfolding card_atLeastAtMost using assms by auto
  finally show ?thesis
    by auto
qed

lemma eval_world_raw_lv: 
  assumes "bexp_wt \<Gamma> exp (Lty ki len)" and "wityping \<Gamma> w"
  shows   "\<exists>bs. eval_world_raw t w exp = Lv ki bs \<and> length bs = len"
  using assms
proof (induction arbitrary: len rule:eval_world_raw.induct)
  case (1 t w e1 e2)
  show ?case
    apply (rule bexp_wt.cases[OF 1(3)])
    using 1 by (auto split:val.split) blast+
next
  case (2 t w e1 e2)
  show ?case 
    apply (rule bexp_wt.cases[OF 2(3)])
    using 2 by (auto split:val.split) blast+
next
  case (3 t w e1 e2)
  show ?case 
    apply (rule bexp_wt.cases[OF 3(3)])
    using 3 by (auto split:val.split) blast+
next
  case (4 t w e1 e2)
  show ?case 
    apply (rule bexp_wt.cases[OF 4(3)])
    using 4 by (auto split:val.split) blast+
next
  case (5 t w e1 e2)
  show ?case 
    apply (rule bexp_wt.cases[OF 5(3)])
    using 5 by (auto split:val.split) blast+
next
  case (6 t w e1 e2)
  show ?case 
    apply (rule bexp_wt.cases[OF 6(3)])
    using 6  by (auto split:val.split) blast+
next
  case (7 t w e1 e2)
  then obtain len1 len2 where *: "bexp_wt \<Gamma> e1 (Lty ki len1) \<and> bexp_wt \<Gamma> e2 (Lty ki len2) \<and> len = max len1 len2 \<and> (ki = Uns \<or> ki = Sig)"
    using bexp_wt_add by blast
  then obtain bs1 bs2 where "eval_world_raw t w e1 = Lv ki bs1 \<and> length bs1 = len1" and 
                            "eval_world_raw t w e2 = Lv ki bs2 \<and> length bs2 = len2"
    using 7 by blast
  thus ?case
    using * size_bin_to_bl by (auto split: signedness.split)
next
  case (8 t w e1 e2)
  then obtain len1 len2 where *: "bexp_wt \<Gamma> e1 (Lty ki len1) \<and> bexp_wt \<Gamma> e2 (Lty ki len2) \<and> len = len1 + len2 \<and> (ki = Uns \<or> ki = Sig)"
    using bexp_wt_mult by blast
  then obtain bs1 bs2 where "eval_world_raw t w e1 = Lv ki bs1 \<and> length bs1 = len1" and 
                            "eval_world_raw t w e2 = Lv ki bs2 \<and> length bs2 = len2"
    using 8 by blast
  thus ?case 
    using * size_bin_to_bl by (auto split: signedness.split val.split)
next
  case (9 t w e1 e2)
  then obtain len1 len2 where *: "bexp_wt \<Gamma> e1 (Lty ki len1) \<and> bexp_wt \<Gamma> e2 (Lty ki len2) \<and> len = max len1 len2 \<and> (ki = Uns \<or> ki = Sig)"
    using bexp_wt_sub by blast
  then obtain bs1 bs2 where "eval_world_raw t w e1 = Lv ki bs1 \<and> length bs1 = len1" and 
                            "eval_world_raw t w e2 = Lv ki bs2 \<and> length bs2 = len2"
    using 9 by blast
  thus ?case 
    using * size_bin_to_bl by (auto split: signedness.split val.split)
next
  case (10 t w sig)
  show ?case
    apply (rule bexp_wt_cases_slice(2)[OF 10(1)])
    using 10  by (smt eval_world_raw.simps(10) ty.distinct(1) ty.inject type_of.elims wityping_def wtyping_def)
next
  case (11 t w)
  then show ?case 
    using bexp_wt.cases[OF 11(1)] by blast+
next
  case (12 t w)
  then show ?case 
    using bexp_wt.cases[OF 12(1)] by blast+
next
  case (13 t w sig dly)
  show ?case 
    apply (rule bexp_wt_cases_del[OF 13(1)])
    using 13 unfolding wityping_def wtyping_def 
    by (smt eval_world_raw.simps(13) styping_def ty.distinct(1) ty.inject type_of.elims)
next
  case (14 t w sig)
  show ?case  
    using bexp_wt.cases[OF 14(1)] by blast+
next
  case (15 t w e)
  hence *: "\<exists>bs. eval_world_raw t w e = Lv ki bs \<and> length bs = len"
    using bexp_wt_cases(1) by blast
  show ?case 
    using 15 *  by (metis eval_world_raw.simps(15) length_map val.simps(6))
next
  case (16 t w sig l r)
  show ?case 
    apply (rule bexp_wt_cases_slice(1)[OF 16(2)])
    using 16 
    apply (auto split:val.split)
    unfolding length_nths using card_slice by auto
next
  case (17 t w sig idx)
  then show ?case
    using bexp_wt_cases_slice(3) by fastforce
next
  case (18 t w e n)
  show ?case 
    apply (rule bexp_wt_cases_shiftl[OF 18(2)])
     apply (auto split:val.split)
    using 18 by auto
next
  case (19 t w e n)
  show ?case 
    apply (rule bexp_wt_cases_shiftr[OF 19(2)])
     apply (auto split:val.split)
    using 19 by auto
next
  case (20 t w th guard el)
  hence *: "\<exists>v. eval_world_raw t w guard = Bv v"
    using bexp_wt_cases_when  by (metis eval_world_raw_bv)
  show ?case 
    apply (rule bexp_wt_cases_when[OF 20(4)])
    using * 20  by (smt eval_world_raw.simps(20) val.simps(5))
next
  case (21 t w sign val)
  then show ?case 
    using bexp_wt_cases_lit  by fastforce
qed  

lemma eval_world_raw_correctness_if:
  assumes "eval_world_raw t w exp = res" 
  assumes "wityping \<Gamma> w" and  "bexp_wt \<Gamma> exp ty"
  shows   "beval_world_raw w t exp res"
  using assms
proof (induct arbitrary: res ty rule: eval_world_raw.induct)
  case (1 t w e1 e2)
  then consider (bool) "ty = Bty" | (vector) ki len where "ty = Lty ki len"
    by (meson ty.exhaust)
  then show ?case 
  proof (cases)
    case bool
    hence "bexp_wt \<Gamma> e1 Bty" and "bexp_wt \<Gamma> e2 Bty"
      using 1(5) bexp_wt.cases by auto
    then obtain res1 res2 where "eval_world_raw t w e1 = Bv res1" and "eval_world_raw t w e2 = Bv res2"
      using eval_world_raw_bv  using "1.prems"(2) by blast
    hence " beval_world_raw w t e1 (Bv res1)" and " beval_world_raw w t e2 (Bv res2)"
      using "1.hyps" "1.prems" \<open>bexp_wt \<Gamma> e1 Bty\<close> \<open>bexp_wt \<Gamma> e2 Bty\<close> by blast+
    moreover have "res = Bv (res1 \<and> res2)"
      using "1.prems"(1) \<open>eval_world_raw t w e1 = Bv res1\<close> \<open>eval_world_raw t w e2 = Bv res2\<close> by auto
    ultimately show ?thesis 
      by (simp add: beval_raw.intros(8) beval_world_raw.simps)
  next
    case vector
    hence "bexp_wt \<Gamma> e1 (Lty ki len)" and "bexp_wt \<Gamma> e2 (Lty ki len)"
      using 1(5) bexp_wt.cases by auto
    then obtain res1 res2 where "eval_world_raw t w e1 = Lv ki res1" and "length res1 = len" 
                            and "eval_world_raw t w e2 = Lv ki res2" and "length res2 = len"
      using eval_world_raw_lv using "1.prems"(2) by blast
    hence " beval_world_raw w t e1 (Lv ki res1) \<and>  beval_world_raw w t e2 (Lv ki res2)"
      using "1.hyps"(1) "1.prems"(2) \<open>bexp_wt \<Gamma> e1 (Lty ki len)\<close> "1.hyps"(2) \<open>bexp_wt \<Gamma> e2 (Lty ki len)\<close> 
      by blast
    moreover have "res = Lv ki (map2 (\<and>) res1 res2)"
      using 1(3) `eval_world_raw t w e1 = Lv ki res1` `eval_world_raw t w e2 = Lv ki res2` 
      by auto
    ultimately show ?thesis 
      by (metis \<open>length res1 = len\<close> \<open>length res2 = len\<close> beval_raw.intros(9) beval_world_raw.cases
      beval_world_raw.intros)  
  qed
next
  case (2 t w e1 e2)
  then consider (bool) "ty = Bty" | (vector) ki len where "ty = Lty ki len"
    by (meson ty.exhaust)
  then show ?case 
  proof (cases)
    case bool
    hence "bexp_wt \<Gamma> e1 Bty" and "bexp_wt \<Gamma> e2 Bty"
      using 2(5) bexp_wt.cases by auto
    then obtain res1 res2 where "eval_world_raw t w e1 = Bv res1" and "eval_world_raw t w e2 = Bv res2"
      using eval_world_raw_bv  using "2.prems"(2) by blast
    hence " beval_world_raw w t e1 (Bv res1)" and " beval_world_raw w t e2 (Bv res2)"
      using "2.hyps" "2.prems" \<open>bexp_wt \<Gamma> e1 Bty\<close> \<open>bexp_wt \<Gamma> e2 Bty\<close> by blast+
    moreover have "res = Bv (res1 \<or> res2)"
      using "2.prems"(1) \<open>eval_world_raw t w e1 = Bv res1\<close> \<open>eval_world_raw t w e2 = Bv res2\<close> by auto
    ultimately show ?thesis 
      by (meson beval_raw.intros(10) beval_world_raw.cases beval_world_raw.intros)
  next
    case vector
    hence "bexp_wt \<Gamma> e1 (Lty ki len)" and "bexp_wt \<Gamma> e2 (Lty ki len)"
      using 2(5) bexp_wt.cases by auto
    then obtain res1 res2 where "eval_world_raw t w e1 = Lv ki res1" and "length res1 = len" 
                            and "eval_world_raw t w e2 = Lv ki res2" and "length res2 = len"
      using eval_world_raw_lv using "2.prems"(2) by blast
    hence " beval_world_raw w t e1 (Lv ki res1) \<and>  beval_world_raw w t e2 (Lv ki res2)"
      using "2.hyps"(1) "2.prems"(2) \<open>bexp_wt \<Gamma> e1 (Lty ki len)\<close> "2.hyps"(2) \<open>bexp_wt \<Gamma> e2 (Lty ki len)\<close> 
      by blast
    moreover have "res = Lv ki (map2 (\<or>) res1 res2)"
      using 2(3) `eval_world_raw t w e1 = Lv ki res1` `eval_world_raw t w e2 = Lv ki res2` 
      by auto
    ultimately show ?thesis 
      by (metis \<open>length res1 = len\<close> \<open>length res2 = len\<close> beval_raw.intros(11) beval_world_raw.cases beval_world_raw.intros) 
  qed
next
  case (3 t w e1 e2)
  then consider (bool) "ty = Bty" | (vector) ki len where "ty = Lty ki len"
    by (meson ty.exhaust)
  then show ?case 
  proof (cases)
    case bool
    hence "bexp_wt \<Gamma> e1 Bty" and "bexp_wt \<Gamma> e2 Bty"
      using 3(5) bexp_wt.cases by auto
    then obtain res1 res2 where "eval_world_raw t w e1 = Bv res1" and "eval_world_raw t w e2 = Bv res2"
      using eval_world_raw_bv  using "3.prems"(2) by blast
    hence " beval_world_raw w t e1 (Bv res1)" and " beval_world_raw w t e2 (Bv res2)"
      using "3.hyps" "3.prems" \<open>bexp_wt \<Gamma> e1 Bty\<close> \<open>bexp_wt \<Gamma> e2 Bty\<close> by blast+
    moreover have "res = Bv (\<not> (res1 \<and> res2))"
      using "3.prems"(1) \<open>eval_world_raw t w e1 = Bv res1\<close> \<open>eval_world_raw t w e2 = Bv res2\<close> by auto
    ultimately show ?thesis 
      by (meson beval_raw.intros(12) beval_world_raw.cases beval_world_raw.intros)
  next
    case vector
    hence "bexp_wt \<Gamma> e1 (Lty ki len)" and "bexp_wt \<Gamma> e2 (Lty ki len)"
      using 3(5) bexp_wt.cases by auto
    then obtain res1 res2 where "eval_world_raw t w e1 = Lv ki res1" and "length res1 = len" 
                            and "eval_world_raw t w e2 = Lv ki res2" and "length res2 = len"
      using eval_world_raw_lv using "3.prems"(2) by blast
    hence " beval_world_raw w t e1 (Lv ki res1) \<and>  beval_world_raw w t e2 (Lv ki res2)"
      using "3.hyps"(1) "3.prems"(2) \<open>bexp_wt \<Gamma> e1 (Lty ki len)\<close> "3.hyps"(2) \<open>bexp_wt \<Gamma> e2 (Lty ki len)\<close> 
      by blast
    moreover have "res = Lv ki (map2 (\<lambda>x y. \<not> (x \<and> y)) res1 res2)"
      using 3(3) `eval_world_raw t w e1 = Lv ki res1` `eval_world_raw t w e2 = Lv ki res2` 
      by auto
    ultimately show ?thesis 
      by (metis \<open>length res1 = len\<close> \<open>length res2 = len\<close> beval_raw.intros(13) beval_world_raw.cases beval_world_raw.intros)
  qed
next
  case (4 t w e1 e2)
  then consider (bool) "ty = Bty" | (vector) ki len where "ty = Lty ki len"
    by (meson ty.exhaust)
  then show ?case 
  proof (cases)
    case bool
    hence "bexp_wt \<Gamma> e1 Bty" and "bexp_wt \<Gamma> e2 Bty"
      using 4(5) bexp_wt.cases by auto
    then obtain res1 res2 where "eval_world_raw t w e1 = Bv res1" and "eval_world_raw t w e2 = Bv res2"
      using eval_world_raw_bv  using "4.prems"(2) by blast
    hence " beval_world_raw w t e1 (Bv res1)" and " beval_world_raw w t e2 (Bv res2)"
      using "4.hyps" "4.prems" \<open>bexp_wt \<Gamma> e1 Bty\<close> \<open>bexp_wt \<Gamma> e2 Bty\<close> by blast+
    moreover have "res = Bv (\<not> (res1 \<or> res2))"
      using "4.prems"(1) \<open>eval_world_raw t w e1 = Bv res1\<close> \<open>eval_world_raw t w e2 = Bv res2\<close> by auto
    ultimately show ?thesis 
      by (meson beval_raw.intros(14) beval_world_raw.cases beval_world_raw.intros)
  next
    case vector
    hence "bexp_wt \<Gamma> e1 (Lty ki len)" and "bexp_wt \<Gamma> e2 (Lty ki len)"
      using 4(5) bexp_wt.cases by auto
    then obtain res1 res2 where "eval_world_raw t w e1 = Lv ki res1" and "length res1 = len" 
                            and "eval_world_raw t w e2 = Lv ki res2" and "length res2 = len"
      using eval_world_raw_lv using "4.prems"(2) by blast
    hence " beval_world_raw w t e1 (Lv ki res1) \<and>  beval_world_raw w t e2 (Lv ki res2)"
      using "4.hyps"(1) "4.prems"(2) \<open>bexp_wt \<Gamma> e1 (Lty ki len)\<close> "4.hyps"(2) \<open>bexp_wt \<Gamma> e2 (Lty ki len)\<close> 
      by blast
    moreover have "res = Lv ki (map2 (\<lambda>x y. \<not> (x \<or> y)) res1 res2)"
      using 4(3) `eval_world_raw t w e1 = Lv ki res1` `eval_world_raw t w e2 = Lv ki res2` 
      by auto
    ultimately show ?thesis
      by (metis \<open>length res1 = len\<close> \<open>length res2 = len\<close> beval_raw.intros(15) beval_world_raw.cases beval_world_raw.intros)
  qed
next
  case (5 t w e1 e2)
  then consider (bool) "ty = Bty" | (vector) ki len where "ty = Lty ki len"
    by (meson ty.exhaust)
  then show ?case 
  proof (cases)
    case bool
    hence "bexp_wt \<Gamma> e1 Bty" and "bexp_wt \<Gamma> e2 Bty"
      using 5(5) bexp_wt.cases by auto
    then obtain res1 res2 where "eval_world_raw t w e1 = Bv res1" and "eval_world_raw t w e2 = Bv res2"
      using eval_world_raw_bv  using "5.prems"(2) by blast
    hence " beval_world_raw w t e1 (Bv res1)" and " beval_world_raw w t e2 (Bv res2)"
      using "5.hyps" "5.prems" \<open>bexp_wt \<Gamma> e1 Bty\<close> \<open>bexp_wt \<Gamma> e2 Bty\<close> by blast+
    moreover have "res = Bv (xor res1 res2)"
      using "5.prems"(1) \<open>eval_world_raw t w e1 = Bv res1\<close> \<open>eval_world_raw t w e2 = Bv res2\<close> by auto
    ultimately show ?thesis 
      by (meson beval_raw.intros(16) beval_world_raw.cases beval_world_raw.intros)
  next
    case vector
    hence "bexp_wt \<Gamma> e1 (Lty ki len)" and "bexp_wt \<Gamma> e2 (Lty ki len)"
      using 5(5) bexp_wt.cases by auto
    then obtain res1 res2 where "eval_world_raw t w e1 = Lv ki res1" and "length res1 = len" 
                            and "eval_world_raw t w e2 = Lv ki res2" and "length res2 = len"
      using eval_world_raw_lv using "5.prems"(2) by blast
    hence " beval_world_raw w t e1 (Lv ki res1) \<and>  beval_world_raw w t e2 (Lv ki res2)"
      using "5.hyps"(1) "5.prems"(2) \<open>bexp_wt \<Gamma> e1 (Lty ki len)\<close> "5.hyps"(2) \<open>bexp_wt \<Gamma> e2 (Lty ki len)\<close> 
      by blast
    moreover have "res = Lv ki (map2 xor res1 res2)"
      using 5(3) `eval_world_raw t w e1 = Lv ki res1` `eval_world_raw t w e2 = Lv ki res2` 
      by auto
    ultimately show ?thesis 
      by (metis \<open>length res1 = len\<close> \<open>length res2 = len\<close> beval_raw.intros(17) beval_world_raw.cases beval_world_raw.intros)
  qed
next
  case (6 t w e1 e2)
  then consider (bool) "ty = Bty" | (vector) ki len where "ty = Lty ki len"
    by (meson ty.exhaust)
  then show ?case 
  proof (cases)
    case bool
    hence "bexp_wt \<Gamma> e1 Bty" and "bexp_wt \<Gamma> e2 Bty"
      using 6(5) bexp_wt.cases by auto
    then obtain res1 res2 where "eval_world_raw t w e1 = Bv res1" and "eval_world_raw t w e2 = Bv res2"
      using eval_world_raw_bv  using "6.prems"(2) by blast
    hence " beval_world_raw w t e1 (Bv res1)" and " beval_world_raw w t e2 (Bv res2)"
      using "6.hyps" "6.prems" \<open>bexp_wt \<Gamma> e1 Bty\<close> \<open>bexp_wt \<Gamma> e2 Bty\<close> by blast+
    moreover have "res = Bv (\<not> (xor res1 res2))"
      using "6.prems"(1) \<open>eval_world_raw t w e1 = Bv res1\<close> \<open>eval_world_raw t w e2 = Bv res2\<close> by auto
    ultimately show ?thesis 
      by (meson beval_raw.intros(18) beval_world_raw.cases beval_world_raw.intros)
  next
    case vector
    hence "bexp_wt \<Gamma> e1 (Lty ki len)" and "bexp_wt \<Gamma> e2 (Lty ki len)"
      using 6(5) bexp_wt.cases by auto
    then obtain res1 res2 where "eval_world_raw t w e1 = Lv ki res1" and "length res1 = len" 
                            and "eval_world_raw t w e2 = Lv ki res2" and "length res2 = len"
      using eval_world_raw_lv using "6.prems"(2) by blast
    hence " beval_world_raw w t e1 (Lv ki res1) \<and>  beval_world_raw w t e2 (Lv ki res2)"
      using "6.hyps"(1) "6.prems"(2) \<open>bexp_wt \<Gamma> e1 (Lty ki len)\<close> "6.hyps"(2) \<open>bexp_wt \<Gamma> e2 (Lty ki len)\<close> 
      by blast
    moreover have "res = Lv ki (map2 (\<lambda>x y. \<not> xor x y) res1 res2)"
      using 6(3) `eval_world_raw t w e1 = Lv ki res1` `eval_world_raw t w e2 = Lv ki res2` 
      by auto
    ultimately show ?thesis 
      by (metis \<open>length res1 = len\<close> \<open>length res2 = len\<close> beval_raw.intros(19) beval_world_raw.cases beval_world_raw.intros)
  qed
next
  case (7 t w e1 e2)
  obtain res1 res2 where " eval_world_raw t w e1 = res1" and " eval_world_raw t w e2 = res2"
    by auto
  obtain ki len1 len2 where "bexp_wt \<Gamma> e1 (Lty ki len1)" and "bexp_wt \<Gamma> e2 (Lty ki len2)" and 
    "ty = Lty ki (max len1 len2)" using bexp_wt_cases_add[OF ` bexp_wt \<Gamma> (Badd e1 e2) ty`] by metis
  hence IH1: "beval_world_raw w t e1 res1" and IH2: "beval_world_raw w t e2 res2"
    using 7(1)[OF `eval_world_raw t w e1 = res1` `wityping \<Gamma> w`]  7(2)[OF `eval_world_raw t w e2 = res2` `wityping \<Gamma> w`]
    by auto
  let ?len1 = "length (lval_of res1)"
  let ?len2 = "length (lval_of res2)"
  have "?len1 = len1" and "?len2 = len2"
    using IH1 `bexp_wt \<Gamma> e1 (Lty ki len1)` `bexp_wt \<Gamma> e2 (Lty ki len2)` IH2 
    by (metis (no_types, lifting) "7.prems"(2) beval_raw_preserve_well_typedness
    beval_world_raw_cases ty.distinct(1) ty.inject type_of.simps(1) type_of.simps(2) val.exhaust_sel
    wityping_def wityping_ensure_styping wityping_ensure_ttyping)+    

  consider (Uns) "ki = Uns" | (Sig) "ki = Sig"
    using `ty = Lty ki (max len1 len2)` "7.prems"(3) bexp_wt_add by blast
  thus ?case
  proof (cases)
    case Uns
    then obtain bs1 bs2 where "res1 = Lv Uns bs1" and "length bs1 = len1" and "res2 = Lv Uns bs2" and "length bs2 = len2"
      using "7.prems"(2) \<open>bexp_wt \<Gamma> e1 (Lty ki len1)\<close> \<open>eval_world_raw t w e1 = res1\<close> eval_world_raw_lv 
      by (metis \<open>bexp_wt \<Gamma> e2 (Lty ki len2)\<close> \<open>eval_world_raw t w e2 = res2\<close>)
    hence "res = Lv Uns (bin_to_bl (max len1 len2) ((bl_to_bin bs1) + (bl_to_bin bs2)))"
      using 7(3) `eval_world_raw t w e1 = res1` `eval_world_raw t w e2 = res2` by auto
    then show ?thesis 
      using IH1 IH2 `res1 = Lv Uns bs1` `res2 = Lv Uns bs2`
      by (metis \<open>length bs1 = len1\<close> \<open>length bs2 = len2\<close> beval_raw.intros(22) beval_world_raw.cases beval_world_raw.intros)
  next
    case Sig
    then obtain bs1 bs2 where "res1 = Lv Sig bs1" and "length bs1 = len1" and "res2 = Lv Sig bs2" and "length bs2 = len2"
      using "7.prems"(2) \<open>bexp_wt \<Gamma> e1 (Lty ki len1)\<close> \<open>eval_world_raw t w e1 = res1\<close> eval_world_raw_lv 
      by (metis \<open>bexp_wt \<Gamma> e2 (Lty ki len2)\<close> \<open>eval_world_raw t w e2 = res2\<close>)
    hence "res = Lv Sig (bin_to_bl (max len1 len2) ((sbl_to_bin bs1) + (sbl_to_bin bs2)))"
      using 7(3) `eval_world_raw t w e1 = res1` `eval_world_raw t w e2 = res2` by auto
    then show ?thesis 
      using IH1 IH2 `res1 = Lv Sig bs1` `res2 = Lv Sig bs2`
      by (metis \<open>length bs1 = len1\<close> \<open>length bs2 = len2\<close> beval_raw.intros(23) beval_world_raw.cases beval_world_raw.intros)
  qed
next
  case (8 t w e1 e2)  
  obtain res1 res2 where " eval_world_raw t w e1 = res1" and " eval_world_raw t w e2 = res2"
    by auto
  obtain ki len1 len2 where "bexp_wt \<Gamma> e1 (Lty ki len1)" and "bexp_wt \<Gamma> e2 (Lty ki len2)" and 
    "ty = Lty ki (len1 + len2)" using bexp_wt_cases_mult[OF ` bexp_wt \<Gamma> (Bmult e1 e2) ty`] by metis
  hence IH1: "beval_world_raw w t e1 res1" and IH2: "beval_world_raw w t e2 res2"
    using 8(1)[OF `eval_world_raw t w e1 = res1` `wityping \<Gamma> w`]  8(2)[OF `eval_world_raw t w e2 = res2` `wityping \<Gamma> w`]
    by auto
  let ?len1 = "length (lval_of res1)"
  let ?len2 = "length (lval_of res2)"
  have "?len1 = len1" and "?len2 = len2"
    using IH1 `bexp_wt \<Gamma> e1 (Lty ki len1)` `bexp_wt \<Gamma> e2 (Lty ki len2)` IH2 
    by (metis (no_types, lifting) "8.prems"(2) beval_raw_preserve_well_typedness
    beval_world_raw_cases ty.distinct(1) ty.inject type_of.simps(1) type_of.simps(2) val.exhaust_sel
    wityping_def wityping_ensure_styping wityping_ensure_ttyping)+    

  consider (Uns) "ki = Uns" | (Sig) "ki = Sig"
    using `ty = Lty ki (len1 + len2)` "8.prems"(3) bexp_wt_mult by blast
  thus ?case
  proof (cases)
    case Uns
    then obtain bs1 bs2 where "res1 = Lv Uns bs1" and "length bs1 = len1" and "res2 = Lv Uns bs2" and "length bs2 = len2"
      using "8.prems"(2) \<open>bexp_wt \<Gamma> e1 (Lty ki len1)\<close> \<open>eval_world_raw t w e1 = res1\<close> eval_world_raw_lv 
      by (metis \<open>bexp_wt \<Gamma> e2 (Lty ki len2)\<close> \<open>eval_world_raw t w e2 = res2\<close>)
    hence "res = Lv Uns (bin_to_bl (len1 + len2) ((bl_to_bin bs1) * (bl_to_bin bs2)))"
      using 8(3) `eval_world_raw t w e1 = res1` `eval_world_raw t w e2 = res2` by auto
    then show ?thesis 
      using IH1 IH2 `res1 = Lv Uns bs1` `res2 = Lv Uns bs2`
      by (metis \<open>length bs1 = len1\<close> \<open>length bs2 = len2\<close> beval_raw.intros(24) beval_world_raw.cases beval_world_raw.intros)
  next
    case Sig
    then obtain bs1 bs2 where "res1 = Lv Sig bs1" and "length bs1 = len1" and "res2 = Lv Sig bs2" and "length bs2 = len2"
      using "8.prems"(2) \<open>bexp_wt \<Gamma> e1 (Lty ki len1)\<close> \<open>eval_world_raw t w e1 = res1\<close> eval_world_raw_lv 
      by (metis \<open>bexp_wt \<Gamma> e2 (Lty ki len2)\<close> \<open>eval_world_raw t w e2 = res2\<close>)
    hence "res = Lv Sig (bin_to_bl (len1 + len2) ((sbl_to_bin bs1) * (sbl_to_bin bs2)))"
      using 8(3) `eval_world_raw t w e1 = res1` `eval_world_raw t w e2 = res2` by auto
    then show ?thesis 
      using IH1 IH2 `res1 = Lv Sig bs1` `res2 = Lv Sig bs2` 
      by (metis \<open>length bs1 = len1\<close> \<open>length bs2 = len2\<close> beval_raw.intros(25) beval_world_raw.cases beval_world_raw.intros)
  qed
next
  case (9 t w e1 e2)
  obtain res1 res2 where " eval_world_raw t w e1 = res1" and " eval_world_raw t w e2 = res2"
    by auto
  obtain ki len1 len2 where "bexp_wt \<Gamma> e1 (Lty ki len1)" and "bexp_wt \<Gamma> e2 (Lty ki len2)" and 
    "ty = Lty ki (max len1 len2)" using bexp_wt_cases_sub[OF ` bexp_wt \<Gamma> (Bsub e1 e2) ty`] by metis
  hence IH1: "beval_world_raw w t e1 res1" and IH2: "beval_world_raw w t e2 res2"
    using 9(1)[OF `eval_world_raw t w e1 = res1` `wityping \<Gamma> w`]  9(2)[OF `eval_world_raw t w e2 = res2` `wityping \<Gamma> w`]
    by auto
  let ?len1 = "length (lval_of res1)"
  let ?len2 = "length (lval_of res2)"
  have "?len1 = len1" and "?len2 = len2"
    using IH1 `bexp_wt \<Gamma> e1 (Lty ki len1)` `bexp_wt \<Gamma> e2 (Lty ki len2)` IH2 
    by (metis (no_types, lifting) "9.prems"(2) beval_raw_preserve_well_typedness
    beval_world_raw_cases ty.distinct(1) ty.inject type_of.simps(1) type_of.simps(2) val.exhaust_sel
    wityping_def wityping_ensure_styping wityping_ensure_ttyping)+    

  consider (Uns) "ki = Uns" | (Sig) "ki = Sig"
    using `ty = Lty ki (max len1 len2)` "9.prems"(3) bexp_wt_sub by blast
  thus ?case
  proof (cases)
    case Uns
    then obtain bs1 bs2 where "res1 = Lv Uns bs1" and "length bs1 = len1" and "res2 = Lv Uns bs2" and "length bs2 = len2"
      using "9.prems"(2) \<open>bexp_wt \<Gamma> e1 (Lty ki len1)\<close> \<open>eval_world_raw t w e1 = res1\<close> eval_world_raw_lv 
      by (metis \<open>bexp_wt \<Gamma> e2 (Lty ki len2)\<close> \<open>eval_world_raw t w e2 = res2\<close>)
    hence "res = Lv Uns (bin_to_bl (max len1 len2) ((bl_to_bin bs1) - (bl_to_bin bs2)))"
      using 9(3) `eval_world_raw t w e1 = res1` `eval_world_raw t w e2 = res2` by auto
    then show ?thesis 
      using IH1 IH2 `res1 = Lv Uns bs1` `res2 = Lv Uns bs2`
      by (metis \<open>length bs1 = len1\<close> \<open>length bs2 = len2\<close> beval_raw.intros(26) beval_world_raw.cases beval_world_raw.intros)
  next
    case Sig
    then obtain bs1 bs2 where "res1 = Lv Sig bs1" and "length bs1 = len1" and "res2 = Lv Sig bs2" and "length bs2 = len2"
      using "9.prems"(2) \<open>bexp_wt \<Gamma> e1 (Lty ki len1)\<close> \<open>eval_world_raw t w e1 = res1\<close> eval_world_raw_lv 
      by (metis \<open>bexp_wt \<Gamma> e2 (Lty ki len2)\<close> \<open>eval_world_raw t w e2 = res2\<close>)
    hence "res = Lv Sig (bin_to_bl (max len1 len2) ((sbl_to_bin bs1) - (sbl_to_bin bs2)))"
      using 9(3) `eval_world_raw t w e1 = res1` `eval_world_raw t w e2 = res2` by auto
    then show ?thesis 
      using IH1 IH2 `res1 = Lv Sig bs1` `res2 = Lv Sig bs2`
      by (metis \<open>length bs1 = len1\<close> \<open>length bs2 = len2\<close> beval_raw.intros(27) beval_world_raw.cases beval_world_raw.intros)
  qed
next
  case (10 t w sig)
  then show ?case 
    by (auto intro!: beval_world_raw.intros beval_raw.intros simp add: state_of_world_def)
next
  case (11 t w)
  then show ?case 
    by (auto intro!: beval_world_raw.intros beval_raw.intros)
next
  case (12 t w)
  then show ?case 
    by (auto intro!: beval_world_raw.intros beval_raw.intros)
next
  case (13 t w sig dly)
  have res_def: "res = (if t - dly < t then snd w sig (t - dly) else if 0 < t then snd w sig (t - 1) else fst w sig)"
    using 13 by auto
                
  have "t - dly < t \<or> t - dly = t"
    by linarith
  moreover
  { assume "t - dly < t"
    hence "signal_of (fst w sig) (derivative_hist_raw w t) sig (t - dly) = snd w sig (t - dly)"
      using signal_of_derivative_hist_raw  by metis
    also have "... = res"
      unfolding res_def using `t - dly < t` by auto
    finally have "signal_of (fst w sig) (derivative_hist_raw w t) sig (t - dly) = res" 
      by auto }
  moreover
  { assume "t - dly = t"
    have "0 < t \<or> t = 0" by auto
    moreover
    { assume " 0 < t"
      hence "signal_of (fst w sig) (derivative_hist_raw w t) sig (t - dly) = snd w sig (t - 1)"
        using `t - dly = t` signal_of_derivative_hist_raw2  by (metis diff_le_self)
      also have "... = res"
        unfolding res_def using `t - dly = t` `0 < t` by auto
      finally have "signal_of (fst w sig) (derivative_hist_raw w t) sig (t - dly) = res" 
        by auto }
    moreover
    { assume "t = 0"
      hence "signal_of (fst w sig) (derivative_hist_raw w t) sig (t - dly) = fst w sig"
        using signal_of_derivative_hist_raw3  by (metis \<open>t - dly = t\<close> diff_le_self)
      also have "... = res"
        unfolding res_def using `t = 0` by auto
      finally have "signal_of (fst w sig) (derivative_hist_raw w t) sig (t - dly) = res" 
        by auto }
    ultimately have "signal_of (fst w sig) (derivative_hist_raw w t) sig (t - dly) = res" 
      by auto }
  ultimately have "signal_of (fst w sig) (derivative_hist_raw w t) sig (t - dly) = res"
    by auto         
  thus ?case
    by (meson beval_raw.intros(4) beval_world_raw.intros)
next
  case (14 t w sig)
  then show ?case 
    by (auto intro!: beval_world_raw.intros beval_raw.intros simp add: event_of_world_def event_of_alt_def)
       (smt beval_raw.intros(5) mem_Collect_eq)+
next
  case (15 t w e)
  hence "bexp_wt \<Gamma> e ty"
    using bexp_wt_cases(1) by blast
  obtain bool ki bs where "eval_world_raw t w e = Bv bool \<or> eval_world_raw t w e = Lv ki bs"
    using val.exhaust_sel by blast
  moreover
  { assume "eval_world_raw t w e = Bv bool"
    hence " beval_world_raw w t e (Bv bool)"
      using 15(1) "15.prems"(2) \<open>bexp_wt \<Gamma> e ty\<close> by blast
    hence " res = Bv (\<not> bool)"
      using 15(2) `eval_world_raw t w e = Bv bool` by auto
    hence ?case
      using `beval_world_raw w t e (Bv bool)` beval_raw.intros(6)
      by (intro beval_world_raw.intros) blast+ }
  moreover
  { assume "eval_world_raw t w e = Lv ki bs"
    hence  "res = Lv ki (map Not bs)"
      using 15(2) by auto
    hence IH : "beval_world_raw w t e (Lv ki bs)"
      using 15  \<open>bexp_wt \<Gamma> e ty\<close> \<open>eval_world_raw t w e = Lv ki bs\<close> by blast
    hence ?case
      using `res = Lv ki (map Not bs)` beval_raw.intros(7)
      by (intro beval_world_raw.intros) blast+ }
  ultimately show ?case
    by auto
next
  case (16 t w sig l r)
  then obtain ki bs where *: "eval_world_raw t w (Bsig sig) = Lv ki bs"
    by (meson bexp_wt_cases_slice(1) eval_world_raw_lv)
  hence IH: "beval_world_raw w t (Bsig sig) (Lv ki bs)"
    using 16  bexp_wt.intros(3) by fastforce
  have "res = Lv ki (nths bs {length bs - l - 1..length bs - r - 1})"
    using * 16 unfolding eval_world_raw.simps by auto
  then show ?case 
    using IH beval_raw.intros(20) 
    by (metis beval_world_raw.cases beval_world_raw.intros)
next
  case (17 t w sig idx)
  then obtain ki bs where *: "eval_world_raw t w (Bsig sig) = Lv ki bs"
    by (meson bexp_wt_cases_slice(3) eval_world_raw_lv)
  hence IH: " beval_world_raw w t (Bsig sig) (Lv ki bs)"
    using 17  using bexp_wt.intros(3) by fastforce
  have "eval_world_raw t w (Bsig sig) = snd w sig t"
    by simp
  hence "res = Bv (bs ! idx)"
    using 17 * unfolding eval_world_raw.simps by auto
  then show ?case 
    using IH beval_raw.intros(21)
    by (metis beval_world_raw.cases beval_world_raw.intros)
next
  case (18 t w e n)
  then obtain ki bs where *: "eval_world_raw t w e = Lv ki bs" 
    by (meson bexp_wt_cases_shiftl eval_world_raw_lv)
  hence IH : "beval_world_raw w t e (Lv ki bs)"
    using 18  bexp_wt_cases_shiftl by force
  have "ki = Uns \<or> ki = Sig"
    using `bexp_wt \<Gamma> (Bshiftl e n) ty` 
    by (metis "*" "18.prems"(2) bexp_wt_cases_shiftl eval_world_raw_lv val.inject(2))
  hence "res =  Lv ki (drop n (bs @ replicate n False))"
    using * 18 unfolding eval_world_raw.simps by auto
  then show ?case 
    using IH 
    by (smt "18.prems"(2) "18.prems"(3) beval_raw.intros(28) beval_raw.intros(29) 
        beval_raw_preserve_well_typedness beval_world_raw.cases beval_world_raw.intros 
        bexp_wt_cases_shiftl ty.inject type_of.simps(2) wityping_def wityping_ensure_styping 
        wityping_ensure_ttyping)
next
  case (19 t w e n)
  then obtain ki bs where *: "eval_world_raw t w e = Lv ki bs"
    by (meson bexp_wt_cases_shiftr eval_world_raw_lv)
  hence IH : "beval_world_raw w t e (Lv ki bs)"
    using 19  by (metis bexp_wt_cases_shiftr)
  have "ki = Uns \<or> ki = Sig"
    using `bexp_wt \<Gamma> (Bshiftr e n) ty` 
    by (metis "*" "19.prems"(2) bexp_wt_cases_shiftr eval_world_raw_lv val.inject(2))
  moreover
  { assume "ki = Uns"
    hence "res = Lv Uns (take (length bs) (replicate n False @ bs))"
      using 19(2) * unfolding eval_world_raw.simps by auto
    hence ?case
      using IH unfolding `ki = Uns` 
      by (meson beval_raw.intros(30) beval_world_raw.cases beval_world_raw.intros) }
  moreover
  { assume "ki = Sig"
    hence "res = Lv Sig (take (length bs) (replicate n (hd bs) @ bs))"
      using 19(2) * unfolding eval_world_raw.simps by auto
    hence ?case
      using IH unfolding `ki = Sig` 
      by (meson beval_raw.intros(31) beval_world_raw.cases beval_world_raw.intros) }
  ultimately show ?case by auto
next
  case (20 t w th guard el)
  hence "bexp_wt \<Gamma> guard Bty"
    using bexp_wt_cases_when[OF 20(6)] by auto
  have " eval_world_raw t w guard = Bv True \<or>  eval_world_raw t w guard = Bv False"
    by (metis "20.prems"(2) \<open>bexp_wt \<Gamma> guard Bty\<close> eval_world_raw_bv val.inject(1))
  moreover
  { assume "eval_world_raw t w guard = Bv True"
    hence IH0: "beval_world_raw w t guard (Bv True)"
      using 20(1)  "20.prems"(2) \<open>bexp_wt \<Gamma> guard Bty\<close> by blast
    have "res = eval_world_raw t w th"
      using `eval_world_raw t w guard = Bv True` 20(4) by auto
    hence " beval_world_raw w t th res"
      using 20(2)  "20.prems"(2) "20.prems"(3) \<open>eval_world_raw t w guard = Bv True\<close> bexp_wt_cases_when by blast
    hence ?case
      using IH0  by (meson beval_raw.intros(32) beval_world_raw.cases beval_world_raw.intros) }
  moreover
  { assume "eval_world_raw t w guard = Bv False"
    hence IH0: "beval_world_raw w t guard (Bv False)"
      using 20(1)  "20.prems"(2) \<open>bexp_wt \<Gamma> guard Bty\<close> by blast
    have "res = eval_world_raw t w el"
      using `eval_world_raw t w guard = Bv False` 20(4) by auto
    hence " beval_world_raw w t el res"
      using 20(3)  "20.prems"(2) "20.prems"(3) \<open>eval_world_raw t w guard = Bv False\<close> bexp_wt_cases_when by blast  
    hence ?case
      by (meson IH0 beval_raw.intros(33) beval_world_raw.cases beval_world_raw.intros) }
  ultimately show ?case
    by auto
next
  case (21 t w sign val)
  then show ?case 
    by (metis beval_raw.intros(34) beval_world_raw.intros eval_world_raw.simps(21))
qed
  
lemma eval_world_raw_correctness_only_if:
  assumes "beval_world_raw w t exp res"
  assumes "wityping \<Gamma> w" and  "bexp_wt \<Gamma> exp ty"
  shows   "eval_world_raw t w exp = res" 
  using assms
  by (metis beval_raw_deterministic beval_world_raw.cases eval_world_raw_correctness_if)

section \<open>Typed hoare logic for sequential statements\<close>

abbreviation eval_world_raw2 where "eval_world_raw2 tw exp \<equiv> eval_world_raw (fst tw) (snd tw) exp"

lemma eval_world_raw2_irrelevant:
  assumes "sig \<notin> set_bexp v"
  shows "eval_world_raw2 a[ sig, dly :=\<^sub>2 eval_world_raw2 a exp] v = eval_world_raw2 a v"
  using assms
  by (induction v)
     (auto simp add: worldline_upd2_def worldline_upd_def event_of_alt_def split: val.splits bool.splits)

lemma eval_world_raw2_irrelevant_inert:
  assumes "sig \<notin> set_bexp v"
  shows "eval_world_raw2 a\<lbrakk> sig, dly :=\<^sub>2 eval_world_raw2 a exp\<rbrakk> v = eval_world_raw2 a v"
  using assms
proof (induction v)
  case (Bwhen v1 v2 v3)
  then show ?case 
    by(auto simp add: worldline_inert_upd2_def worldline_inert_upd_def event_of_alt_def split: val.splits bool.splits) presburger+
qed(auto simp add: worldline_inert_upd2_def worldline_inert_upd_def event_of_alt_def)

lemma eval_world_raw2_simp:
  assumes "0 < dly"
  shows " eval_world_raw2 tw[ sig, dly :=\<^sub>2 v] expr = eval_world_raw2 tw expr"
  using assms
  by (induction expr)
     (auto simp add: worldline_upd2_def worldline_upd_def event_of_alt_def split:val.splits bool.splits)

lemma eval_world_raw2_suc[simp]:
  "eval_world_raw2 (tw[ sig, 1 :=\<^sub>2 v]) exp = eval_world_raw2 tw exp"
  by (induction exp)
     (auto simp add: worldline_upd2_def worldline_upd_def event_of_alt_def split:val.splits bool.splits)

lemma type_of_eval_world_raw2:
  assumes "bexp_wt \<Gamma> expr ty"
  shows "\<And>tw. wityping \<Gamma> (snd tw) \<Longrightarrow> type_of (eval_world_raw2 tw expr) = ty"
  using assms
proof (induction expr arbitrary: ty)
  case (Bsig x)
  then show ?case 
    by (metis bexp_wt_cases_slice(2) eval_world_raw.simps(10) wityping_def wtyping_def)
next
  case (Bsig_event x)
  have "ty = Bty"
    using bexp_wt_cases_all[OF Bsig_event(2)] by auto
  then show ?case 
    by auto
next
  case (Bsig_delayed x1a x2a)
  hence "ty = \<Gamma> x1a"
    using bexp_wt_cases_all[OF Bsig_delayed(2)] by auto    
  then show ?case 
    using Bsig_delayed(1) unfolding wityping_def wtyping_def styping_def
    by auto
next
  case (Bnot expr)
  hence "bexp_wt \<Gamma> expr ty"
    using bexp_wt_cases(1)[OF Bnot(3)] by blast
  then show ?case 
    using Bnot(1)[OF Bnot(2)]  by (auto split:val.splits)
next
  case (Band expr1 expr2)
  moreover hence " type_of (eval_world_raw2 tw expr1) = ty"
    using bexp_wt_cases(2) by blast
  moreover have "type_of (eval_world_raw2 tw expr2) = ty"
    using Band.IH(2) Band.prems(1) Band.prems(2) bexp_wt_cases(2) by blast
  ultimately show ?case 
    by (auto split:val.splits)
next
  case (Bor expr1 expr2)
  moreover hence " type_of (eval_world_raw2 tw expr1) = ty"
    using bexp_wt_cases(3) by blast
  moreover have "type_of (eval_world_raw2 tw expr2) = ty"
    by (meson bexp_wt_cases(3) calculation(2) calculation(3) calculation(4))
  ultimately show ?case 
    by (auto split: val.splits)
next
  case (Bnand expr1 expr2)
  moreover hence " type_of (eval_world_raw2 tw expr1) = ty"
    using bexp_wt_cases(4) by blast
  moreover have "type_of (eval_world_raw2 tw expr2) = ty"
    by (meson bexp_wt_cases(4) calculation(2) calculation(3) calculation(4))
  ultimately show ?case 
    by (auto split:val.splits)
next
  case (Bnor expr1 expr2)
  moreover hence " type_of (eval_world_raw2 tw expr1) = ty"
    using bexp_wt_cases(5) by blast
  moreover have "type_of (eval_world_raw2 tw expr2) = ty"
    by (meson bexp_wt_cases(5) calculation(2) calculation(3) calculation(4))
  ultimately show ?case 
    by (auto split:val.splits)
next
  case (Bxor expr1 expr2)
  moreover hence " type_of (eval_world_raw2 tw expr1) = ty"
    using bexp_wt_cases(6) by blast
  moreover have "type_of (eval_world_raw2 tw expr2) = ty"
    by (meson bexp_wt_cases(6) calculation(2) calculation(3) calculation(4))
  ultimately show ?case 
    by (auto split:val.splits)
next
  case (Bxnor expr1 expr2)
  moreover hence " type_of (eval_world_raw2 tw expr1) = ty"
    using bexp_wt_cases(7) by blast
  moreover have "type_of (eval_world_raw2 tw expr2) = ty"
    by (meson bexp_wt_cases(7) calculation(2) calculation(3) calculation(4))
  ultimately show ?case 
    by (auto split:val.splits)
next
  case Btrue
  have "ty = Bty"
    using bexp_wt_cases_all[OF Btrue(2)] by auto
  then show ?case 
    by auto
next
  case Bfalse
  have "ty = Bty"
    using bexp_wt_cases_all[OF Bfalse(2)] by auto
  then show ?case 
    by auto
next
  case (Bslice x1a x2a x3)
  show ?case  
    by (metis Bslice.prems(1) Bslice.prems(2) bexp_wt_cases_slice(1) eval_world_raw_lv type_of.simps(2))
next
  case (Bindex x1a x2a)
  then show ?case 
    by (metis bexp_wt_cases_slice(3) eval_world_raw_bv type_of.simps(1))
next
  case (Badd expr1 expr2)
  then obtain ki len1 where *: " type_of (eval_world_raw2 tw expr1) = Lty ki len1"
    using bexp_wt_cases_add[OF Badd(4)]  by (metis eval_world_raw_lv type_of.simps(2))
  then obtain ki len2 where **: "type_of (eval_world_raw2 tw expr2) = Lty ki len2"
    using bexp_wt_cases_add[OF Badd(4)]  by (metis Badd(3) eval_world_raw_lv type_of.simps(2))
  hence "ty = Lty ki (max len1 len2)"
    using bexp_wt_cases_add[OF Badd(4)] 
    by (smt Badd.prems(1) * eval_world_raw_lv ty.inject type_of.simps(2))
  then show ?case 
    using * **
    by (metis Badd.prems(1) Badd.prems(2) eval_world_raw_lv type_of.simps(2))
next
  case (Bmult expr1 expr2)
  then obtain ki len1 where *: " type_of (eval_world_raw2 tw expr1) = Lty ki len1"
    using bexp_wt_cases_mult[OF Bmult(4)]  by (metis eval_world_raw_lv type_of.simps(2))
  then obtain ki len2 where **: "type_of (eval_world_raw2 tw expr2) = Lty ki len2"
    using bexp_wt_cases_mult[OF Bmult(4)]   by (metis Bmult(3) eval_world_raw_lv type_of.simps(2))
  hence "ty = Lty ki (len1  + len2)"
    using bexp_wt_cases_mult[OF Bmult(4)] 
    by (smt "*" Bmult(3) eval_world_raw_lv ty.inject type_of.simps(2))
  then show ?case 
    using * ** by (metis Bmult.prems(1) Bmult.prems(2) eval_world_raw_lv type_of.simps(2))
next
  case (Bsub expr1 expr2)
  then obtain ki len1 where *: " type_of (eval_world_raw2 tw expr1) = Lty ki len1"
    using bexp_wt_cases_sub[OF Bsub(4)]  by (metis eval_world_raw_lv type_of.simps(2))
  then obtain ki len2 where **: "type_of (eval_world_raw2 tw expr2) = Lty ki len2"
    using bexp_wt_cases_sub[OF Bsub(4)]  by (metis Bsub.prems(1) eval_world_raw_lv type_of.simps(2))
  hence "ty = Lty ki (max len1 len2)"
    using bexp_wt_cases_sub[OF Bsub(4)]  by (smt "*" Bsub.prems(1) eval_world_raw_lv ty.inject type_of.simps(2))
  then show ?case 
    using * **  by (metis Bsub.prems(1) Bsub.prems(2) eval_world_raw_lv type_of.simps(2))
next
  case (Bshiftl expr x2a)
  then obtain ki len where "ty = Lty ki len" and "0 < len"
    using bexp_wt_cases_shiftl[OF Bshiftl(3)] by metis
  then show ?case 
    by (metis Bshiftl.prems(1) Bshiftl.prems(2) eval_world_raw_lv type_of.simps(2))
next
  case (Bshiftr expr x2a)
  then obtain ki len where "ty = Lty ki len" and "0 < len"
    using bexp_wt_cases_shiftr[OF Bshiftr(3)] by metis
  then show ?case 
    by (metis Bshiftr.prems(1) Bshiftr.prems(2) eval_world_raw_lv type_of.simps(2))
next
  case (Bwhen expr1 expr2 expr3)
  hence "bexp_wt \<Gamma> expr2 Bty"
    using bexp_wt_cases_when[OF Bwhen(5)]  by blast
  hence *: "type_of (eval_world_raw2 tw expr2) = Bty"
    using Bwhen  by blast
  have "bexp_wt \<Gamma> expr3 ty" and "bexp_wt \<Gamma> expr1 ty"
    using bexp_wt_cases_when[OF Bwhen(5)]  by blast+
  hence "type_of (eval_world_raw2 tw expr1) = ty" and "type_of (eval_world_raw2 tw expr3) = ty"
    using Bwhen by blast+
  then show ?case 
    using * by (auto split:val.splits bool.splits)
next
  case (Bliteral x1a x2a)
  then show ?case 
    using bexp_wt_cases_lit by fastforce
qed

lemma worldline_upd_eval_world_raw_preserve_wityping:
  assumes "wityping \<Gamma> (snd tw)"
  assumes "bexp_wt \<Gamma> expr (\<Gamma> sig)"
  shows   "wityping \<Gamma> (snd (tw[ sig, t :=\<^sub>2 eval_world_raw2 tw expr]))"
  using assms 
  by (simp add: type_of_eval_world_raw2 worldline_upd2_def worldline_upd_preserve_wityping)

lemma worldline_upd_eval_world_raw_preserve_wityping2:
  assumes "wityping \<Gamma> (snd tw)"
  assumes "type_of v = \<Gamma> sig"
  shows   "wityping \<Gamma> (snd (tw[ sig, t :=\<^sub>2 v]))"
  using assms
  by (simp add: worldline_upd2_def worldline_upd_preserve_wityping)

inductive
  seq_hoare3 :: "'signal tyenv \<Rightarrow> 'signal assn2 \<Rightarrow> 'signal seq_stmt \<Rightarrow> 'signal assn2 \<Rightarrow> bool" ("  (1_) \<turnstile> ([(1_)]/ (_)/ [(1_)])" 50)
  where
  Null3: " \<Gamma> \<turnstile> [P] Bnull [P]"

| Assign3: "\<Gamma> \<turnstile> [\<lambda>tw. P(tw[sig, dly :=\<^sub>2 eval_world_raw2 tw exp])] Bassign_trans sig exp dly [P]"

| AssignI3: "\<Gamma> \<turnstile> [\<lambda>tw. P( tw\<lbrakk>sig, dly :=\<^sub>2 eval_world_raw2 tw exp\<rbrakk>)] Bassign_inert sig exp dly [P]"

| Comp3: "\<lbrakk> \<Gamma> \<turnstile> [P] s1 [Q]; \<Gamma> \<turnstile> [Q] s2 [R]\<rbrakk> \<Longrightarrow> \<Gamma> \<turnstile> [P] Bcomp s1 s2 [R]"

| If3: "\<lbrakk>\<Gamma> \<turnstile> [\<lambda>tw. P tw \<and> eval_world_raw2 tw g = (Bv True)] s1 [Q];
         \<Gamma> \<turnstile> [\<lambda>tw. P tw \<and> eval_world_raw2 tw g = (Bv False)] s2 [Q]\<rbrakk>
        \<Longrightarrow>  \<Gamma> \<turnstile> [P] Bguarded g s1 s2 [Q]"

| Conseq3: "\<lbrakk>\<forall>tw. wityping \<Gamma> (snd tw) \<and> P' tw \<longrightarrow> P tw; \<Gamma> \<turnstile> [P] s [Q]; \<forall>tw. Q tw \<longrightarrow> Q' tw\<rbrakk> \<Longrightarrow> \<Gamma> \<turnstile> [P'] s [Q']"

| Conj3: "\<Gamma> \<turnstile> [P] s [Q1] \<Longrightarrow>  \<Gamma> \<turnstile> [P] s [Q2] \<Longrightarrow>  \<Gamma> \<turnstile> [P] s [\<lambda>tw. Q1 tw \<and> Q2 tw]"

| Bcase_empty_choices3: " \<Gamma> \<turnstile> [P] Bcase exp [] [P]"

| Bcase_others3: " \<Gamma> \<turnstile> [P] ss [Q] \<Longrightarrow>  \<Gamma> \<turnstile> [P] Bcase exp ((Others, ss) # choices) [Q]"

| Bcase_if3: "\<Gamma> \<turnstile> [\<lambda>tw.  P tw \<and> (eval_world_raw2 tw exp = eval_world_raw2 tw exp')] ss [Q]
  \<Longrightarrow> \<Gamma> \<turnstile> [\<lambda>tw. P tw \<and> (eval_world_raw2 tw exp \<noteq> eval_world_raw2 tw exp')] Bcase exp choices [Q]
  \<Longrightarrow>  \<Gamma> \<turnstile> [P] Bcase exp ((Explicit exp', ss) # choices) [Q]"

lemma seq_hoare3_soundness:
  assumes "\<Gamma> \<turnstile> [P] ss [Q]"
  assumes "seq_wt \<Gamma> ss" and  "nonneg_delay ss"
  shows   "\<Gamma> \<Turnstile> [P] ss [Q]"
  using assms
proof (induction rule:seq_hoare3.induct)
  case (Null3 P)
  then show ?case 
    unfolding seq_hoare_valid2_wt_def 
    using world_seq_exec_bnull world_seq_exec_deterministic by blast
next
  case (Assign3 \<Gamma> P sig dly exp)
  then obtain ty where "bexp_wt \<Gamma> exp ty" and "0 < dly"
    by auto
  then show ?case 
    unfolding seq_hoare_valid2_wt_def 
    by (metis beval_world_raw2_def eval_world_raw_correctness_only_if lift_world_trans_worldline_upd2)
next
  case (AssignI3 \<Gamma> P sig dly exp)
  then obtain ty where "bexp_wt \<Gamma> exp ty" and "0 < dly"
    by auto
  then show ?case 
    unfolding seq_hoare_valid2_wt_def 
    by (metis beval_world_raw2_def eval_world_raw_correctness_only_if lift_world_inert_worldline_upd2)
next
  case (Comp3 \<Gamma> P s1 Q s2 R)
  hence " \<Gamma> \<Turnstile> [P] s1 [Q]" and " \<Gamma> \<Turnstile> [Q] s2 [R]"
    using nonneg_delay.simps(2) by blast+
  then show ?case 
    unfolding seq_hoare_valid2_wt_def using Comp3(6) world_seq_exec_comp
    by (smt Comp3.prems(1) nonneg_delay.simps(2) seq_hoare_valid2_def seq_stmt_preserve_wityping_hoare 
        seq_wt_cases(2) soundness_hoare2 world_seq_exec_alt_cases(2) world_seq_exec_alt_imp_world_seq_exec 
        world_seq_exec_imp_world_seq_exec_alt)
next
  case (If3 \<Gamma> P g s1 Q s2)
  have "nonneg_delay s1" and "nonneg_delay s2"
    using If3  nonneg_delay.simps(3) by blast+
  have "\<Gamma> \<Turnstile> [\<lambda>a. P a \<and> eval_world_raw2 a g = Bv True] s1 [Q]" and " \<Gamma> \<Turnstile> [\<lambda>a. P a \<and> eval_world_raw2 a g = Bv False] s2 [Q]"
    using If3 nonneg_delay.simps(3) by blast+
  then show ?case 
    unfolding seq_hoare_valid2_wt_def world_seq_exec_alt_def[OF If3(6), THEN sym]
    world_seq_exec_alt_def[OF `nonneg_delay s1`, THEN sym] world_seq_exec_alt_def[OF `nonneg_delay s2`, THEN sym]
    by (metis If3.prems(1) beval_world_raw2_def eval_world_raw_correctness_only_if seq_wt_cases(3) world_seq_exec_alt_cases(3))
next
  case (Conseq3 \<Gamma> P' P s Q Q')
  hence " \<Gamma> \<Turnstile> [P] s [Q]"  by blast
  then show ?case 
    using Conseq3(1) Conseq3(3) unfolding seq_hoare_valid2_wt_def  by blast 
next
  case (Conj3 \<Gamma> P s Q1 Q2)
  hence "\<Gamma> \<Turnstile> [P] s [Q1]" and "\<Gamma> \<Turnstile> [P] s [Q1]"
    by blast+
  then show ?case 
    unfolding seq_hoare_valid2_wt_def  
    by (metis Conj3.IH(2) Conj3.prems(1) Conj3.prems(2) seq_hoare_valid2_wt_def)
next 
  case (Bcase_empty_choices3 \<Gamma> P exp)
  then show ?case 
    unfolding seq_hoare_valid2_wt_def  using world_seq_exec_bcase_empty world_seq_exec_deterministic by blast
next
  case (Bcase_others3 \<Gamma> P ss Q exp choices)
  hence "seq_wt \<Gamma> ss "
    using seq_wt.cases by auto
  moreover have "nonneg_delay ss"
    using Bcase_others3 by auto
  ultimately have " \<Gamma> \<Turnstile> [P] ss [Q]"
    using Bcase_others3(2) by auto
  then show ?case 
    unfolding seq_hoare_valid2_wt_def  using bcase_others_tw_elim by blast 
next
  case (Bcase_if3 \<Gamma> P exp exp' ss Q choices)
  hence "seq_wt \<Gamma> ss" and "seq_wt \<Gamma> (Bcase exp choices)"
    using seq_wt_cases_bcase by auto
  moreover obtain ty where ty: "bexp_wt \<Gamma> exp ty \<and> bexp_wt \<Gamma> exp' ty"
    using Bcase_if3.prems(1) seq_wt_cases_bcase by force
  moreover have " nonneg_delay ss" and "nonneg_delay (Bcase exp choices)"
    using Bcase_if3(6) by auto
  ultimately have 1: "\<Gamma> \<Turnstile> [\<lambda>a. P a \<and> eval_world_raw2 a exp = eval_world_raw2 a exp'] ss [Q]" and 
    2: "\<Gamma> \<Turnstile> [\<lambda>a. P a \<and> eval_world_raw2 a exp \<noteq> eval_world_raw2 a exp'] Bcase exp choices [Q]"
    using Bcase_if3(3-4) by auto
  show ?case 
    unfolding seq_hoare_valid2_wt_def  world_seq_exec_alt_def[OF Bcase_if3(6), THEN sym]
  proof (intro allI, intro impI)
    fix tw tw' :: "nat \<times> ('a \<Rightarrow> val) \<times> ('a \<Rightarrow> nat \<Rightarrow> val)"
    assume asm: "wityping \<Gamma> (snd tw) \<and> P tw \<and> world_seq_exec_alt tw (Bcase exp ((Explicit exp', ss) # choices)) tw'"
    hence "world_seq_exec_alt tw (Bcase exp ((Explicit exp', ss) # choices)) tw'"
      by auto
    have "eval_world_raw2 tw exp = eval_world_raw2 tw exp' \<or> eval_world_raw2 tw exp \<noteq> eval_world_raw2 tw exp'"
      by auto
    moreover
    { assume "eval_world_raw2 tw exp = eval_world_raw2 tw exp'"
      obtain res where " beval_world_raw (snd tw) (fst tw) exp res"
        using eval_world_raw_correctness_if ty asm  by blast
      obtain res' where "beval_world_raw (snd tw) (fst tw) exp' res'"
        using eval_world_raw_correctness_if ty asm by blast
      hence "world_seq_exec_alt tw ss tw'"
        using world_seq_exec_alt.cases[OF `world_seq_exec_alt tw (Bcase exp ((Explicit exp', ss) # choices)) tw'`]
        by (smt Pair_inject \<open>eval_world_raw2 tw exp = eval_world_raw2 tw exp'\<close> asm beval_world_raw2_def 
            choices.inject eval_world_raw_correctness_only_if list.distinct(1) list.inject 
            seq_stmt.distinct(29) seq_stmt.distinct(9) seq_stmt.inject(5) seq_stmt.simps(23) 
            seq_stmt.simps(29) seq_stmt.simps(33) ty) 
      hence "Q tw'"
        by (metis (mono_tags, lifting) "1" \<open>eval_world_raw2 tw exp = eval_world_raw2 tw exp'\<close> 
            \<open>nonneg_delay ss\<close> asm seq_hoare_valid2_wt_def world_seq_exec_alt_imp_world_seq_exec) }
    moreover
    { assume "eval_world_raw2 tw exp \<noteq> eval_world_raw2 tw exp'"
      obtain res where " beval_world_raw (snd tw) (fst tw) exp res"
        using eval_world_raw_correctness_if ty asm  by blast
      obtain res' where "beval_world_raw (snd tw) (fst tw) exp' res'"
        using eval_world_raw_correctness_if ty asm by blast    
      hence "world_seq_exec_alt tw (Bcase exp choices) tw'"
        using world_seq_exec_alt.cases[OF `world_seq_exec_alt tw (Bcase exp ((Explicit exp', ss) # choices)) tw'`]
        by (smt Pair_inject \<open>eval_world_raw2 tw exp \<noteq> eval_world_raw2 tw exp'\<close> asm beval_world_raw2_def 
                choices.distinct(1) choices.inject eval_world_raw_correctness_only_if list.distinct(1) 
                list.inject seq_stmt.distinct(29) seq_stmt.distinct(9) seq_stmt.inject(5) seq_stmt.simps(23) 
                seq_stmt.simps(29) seq_stmt.simps(33) ty) 
      hence "Q tw'"
        by (smt "2" \<open>eval_world_raw2 tw exp \<noteq> eval_world_raw2 tw exp'\<close> \<open>nonneg_delay (Bcase exp choices)\<close> 
                asm seq_hoare_valid2_wt_def world_seq_exec_alt_imp_world_seq_exec) }
    ultimately show "Q tw'"
      by auto
  qed
qed

text \<open>weakest precondition for typed hoare logic\<close>

definition wp3 :: "'signal tyenv \<Rightarrow> 'signal seq_stmt \<Rightarrow> 'signal assn2 \<Rightarrow> 'signal assn2" where
  "wp3 \<Gamma> ss Q = (\<lambda>tw. wityping \<Gamma> (snd tw) \<and> (\<forall>tw'. (tw, ss \<Rightarrow>\<^sub>s tw') \<longrightarrow> Q tw'))"

lemma wp3_bnull:
  "wp3 \<Gamma> Bnull Q = (\<lambda>tw. Q tw \<and> wityping \<Gamma> (snd tw))"
  apply (rule ext)
  unfolding wp3_def
  using world_seq_exec_bnull world_seq_exec_deterministic by blast

lemma wp3_bcomp:
  assumes "seq_wt \<Gamma> (Bcomp ss1 ss2)" and "nonneg_delay (Bcomp ss1 ss2)"
  shows "wp3 \<Gamma> (Bcomp ss1 ss2) Q = wp3 \<Gamma> ss1 (wp3 \<Gamma> ss2 Q)"
  apply (rule ext)
  unfolding wp3_def
proof (rule, rule, simp, rule, rule, rule)
  fix x tw' :: "nat \<times> ('a \<Rightarrow> val) \<times> ('a \<Rightarrow> nat \<Rightarrow> val)"
  have "seq_wt \<Gamma> ss1" and "seq_wt \<Gamma> ss2"
    using assms by blast+
  assume asm: "wityping \<Gamma> (snd x) \<and> (\<forall>tw'. x, Bcomp ss1 ss2 \<Rightarrow>\<^sub>s tw' \<longrightarrow> Q tw')" and "x, ss1 \<Rightarrow>\<^sub>s tw'" 
  thus " wityping \<Gamma> (snd tw')"
    using soundness_hoare2[OF seq_stmt_preserve_wityping_hoare[OF `seq_wt \<Gamma> ss1`]] assms(2)
    unfolding seq_hoare_valid2_def  using nonneg_delay.simps(2) by blast

  { fix tw2 
    assume "tw', ss2 \<Rightarrow>\<^sub>s tw2"
    hence "x, Bcomp ss1 ss2 \<Rightarrow>\<^sub>s tw2"
      using `x, ss1 \<Rightarrow>\<^sub>s tw'`  using assms(2) world_seq_exec_comp by blast
    with asm  have " Q tw2" by blast
    moreover have "wityping \<Gamma> (snd tw2)"
      using  `wityping \<Gamma> (snd tw')` `tw', ss2 \<Rightarrow>\<^sub>s tw2` soundness_hoare2[OF seq_stmt_preserve_wityping_hoare[OF `seq_wt \<Gamma> ss2`]] assms(2)
      unfolding seq_hoare_valid2_def   using nonneg_delay.simps(2) by blast
    ultimately have "Q tw2 \<and> wityping \<Gamma> (snd tw2)"
      by auto }
  thus " \<forall>tw'a. tw', ss2 \<Rightarrow>\<^sub>s tw'a \<longrightarrow> Q tw'a"
    by auto
next
  fix x
  assume *: " wityping \<Gamma> (snd x) \<and> (\<forall>tw'. x, ss1 \<Rightarrow>\<^sub>s tw' \<longrightarrow> wityping \<Gamma> (snd tw') \<and> (\<forall>tw'a. tw', ss2 \<Rightarrow>\<^sub>s tw'a \<longrightarrow> Q tw'a))"
  hence "(\<forall>tw'. x, Bcomp ss1 ss2 \<Rightarrow>\<^sub>s tw' \<longrightarrow> Q tw')"
    by (meson assms(2) nonneg_delay.simps(2) world_seq_exec_alt_cases(2) world_seq_exec_alt_imp_world_seq_exec world_seq_exec_imp_world_seq_exec_alt)
  moreover have "wityping \<Gamma> (snd x)"
    using * by auto
  ultimately show "wityping \<Gamma> (snd x) \<and> (\<forall>tw'. x, Bcomp ss1 ss2 \<Rightarrow>\<^sub>s tw' \<longrightarrow> Q tw')"
    by auto
qed

lemma wp3_bguarded:
  assumes "seq_wt \<Gamma> (Bguarded g ss1 ss2)" and "nonneg_delay (Bguarded g ss1 ss2)"
  shows "wp3 \<Gamma> (Bguarded g ss1 ss2) Q = (\<lambda>tw. if eval_world_raw2 tw g = Bv True then 
                                                wp3 \<Gamma> ss1 Q tw 
                                              else 
                                                wp3 \<Gamma> ss2 Q tw)"
  apply (rule ext)
  unfolding wp3_def
proof (rule)
  fix tw
  obtain ty where bwt: "bexp_wt \<Gamma> g ty" and "seq_wt \<Gamma> ss1" and "seq_wt \<Gamma> ss2"
    using assms  by blast
  assume asm: " wityping \<Gamma> (snd tw) \<and> (\<forall>tw'. tw, Bguarded g ss1 ss2 \<Rightarrow>\<^sub>s tw' \<longrightarrow> Q tw')"
  hence wt: "wityping \<Gamma> (snd tw)" by auto
  have "eval_world_raw2 tw g = Bv True \<or> eval_world_raw2 tw g \<noteq> Bv True"
    by auto
  moreover
  { assume "eval_world_raw2 tw g = Bv True"
    hence "beval_world_raw2 tw g (Bv True)"
      using eval_world_raw_correctness_if[OF _ wt bwt] by (simp add: beval_world_raw2_def)
    { fix tw'
      assume "tw, ss1 \<Rightarrow>\<^sub>s tw'"
      hence "Q tw'"
        using asm world_seq_exec_guarded[OF `beval_world_raw2 tw g (Bv True)` `tw, ss1 \<Rightarrow>\<^sub>s tw'`]
        by blast 
      moreover have "wityping \<Gamma> (snd tw')"
        using soundness_hoare2[OF seq_stmt_preserve_wityping_hoare[OF `seq_wt \<Gamma> ss1`]] assms(2)
        unfolding seq_hoare_valid2_def using `tw, ss1 \<Rightarrow>\<^sub>s tw'`  using nonneg_delay.simps(3) wt by blast
      ultimately have "Q tw' \<and> wityping \<Gamma> (snd tw')"
        by auto }
    hence "(\<forall>tw'. tw, ss1 \<Rightarrow>\<^sub>s tw' \<longrightarrow> Q tw' \<and> wityping \<Gamma> (snd tw'))"
      by auto
    hence "if eval_world_raw2 tw g = Bv True then wityping \<Gamma> (snd tw) \<and> (\<forall>tw'. tw, ss1 \<Rightarrow>\<^sub>s tw' \<longrightarrow> Q tw' \<and> wityping \<Gamma> (snd tw'))
          else wityping \<Gamma> (snd tw) \<and> (\<forall>tw'. tw, ss2 \<Rightarrow>\<^sub>s tw' \<longrightarrow> Q tw' \<and> wityping \<Gamma> (snd tw'))"
      using wt `eval_world_raw2 tw g = Bv True` by auto }
  moreover
  { assume "eval_world_raw2 tw g \<noteq> Bv True"
    hence  "eval_world_raw2 tw g = Bv False"
      by (metis assms(1) eval_world_raw_bv seq_wt_cases(3) wt)
    hence "beval_world_raw2 tw g (Bv False)"
      using eval_world_raw_correctness_if[OF _ wt bwt] by (simp add: beval_world_raw2_def)
    { fix tw'
      assume "tw, ss2 \<Rightarrow>\<^sub>s tw'"
      hence "Q tw'"
        using asm world_seq_exec_guarded_not[OF `beval_world_raw2 tw g (Bv False)` `tw, ss2 \<Rightarrow>\<^sub>s tw'`]
        by blast 
      moreover have "wityping \<Gamma> (snd tw')"
        using soundness_hoare2[OF seq_stmt_preserve_wityping_hoare[OF `seq_wt \<Gamma> ss2`]] assms(2)
        unfolding seq_hoare_valid2_def using `tw, ss2 \<Rightarrow>\<^sub>s tw'`  using nonneg_delay.simps(3) wt by blast
      ultimately have "Q tw' \<and> wityping \<Gamma> (snd tw')"
        by auto }
    hence "(\<forall>tw'. tw, ss2 \<Rightarrow>\<^sub>s tw' \<longrightarrow> Q tw' \<and> wityping \<Gamma> (snd tw'))"
      by auto    
    hence "if eval_world_raw2 tw g = Bv True then wityping \<Gamma> (snd tw) \<and> (\<forall>tw'. tw, ss1 \<Rightarrow>\<^sub>s tw' \<longrightarrow> Q tw' \<and> wityping \<Gamma> (snd tw'))
          else wityping \<Gamma> (snd tw) \<and> (\<forall>tw'. tw, ss2 \<Rightarrow>\<^sub>s tw' \<longrightarrow> Q tw' \<and> wityping \<Gamma> (snd tw'))"
      using wt `eval_world_raw2 tw g = Bv False` by auto }
  ultimately show "if eval_world_raw2 tw g = Bv True then wityping \<Gamma> (snd tw) \<and> (\<forall>tw'. tw, ss1 \<Rightarrow>\<^sub>s tw' \<longrightarrow> Q tw')
          else wityping \<Gamma> (snd tw) \<and> (\<forall>tw'. tw, ss2 \<Rightarrow>\<^sub>s tw' \<longrightarrow> Q tw')" by auto
next
  fix tw
  assume *: "if eval_world_raw2 tw g = Bv True then wityping \<Gamma> (snd tw) \<and> (\<forall>tw'. tw, ss1 \<Rightarrow>\<^sub>s tw' \<longrightarrow> Q tw')
          else wityping \<Gamma> (snd tw) \<and> (\<forall>tw'. tw, ss2 \<Rightarrow>\<^sub>s tw' \<longrightarrow> Q tw')"
  hence " wityping \<Gamma> (snd tw)"
    by presburger
  { fix tw' 
    assume "tw, Bguarded g ss1 ss2 \<Rightarrow>\<^sub>s tw'"
    hence "Q tw'"
      using * 
      by (smt assms(1) assms(2) beval_world_raw2_def eval_world_raw_correctness_only_if 
          nonneg_delay.simps(3) seq_wt_cases(3) val.simps(1) world_seq_exec_alt_cases(3) 
          world_seq_exec_alt_imp_world_seq_exec world_seq_exec_imp_world_seq_exec_alt) }
  thus "wityping \<Gamma> (snd tw) \<and> (\<forall>tw'. tw, Bguarded g ss1 ss2 \<Rightarrow>\<^sub>s tw' \<longrightarrow> Q tw')"
    using `wityping \<Gamma> (snd tw)` by auto
qed

lemma wp3_bcase_empty:
  "wp3 \<Gamma> (Bcase exp []) Q = (\<lambda>tw. Q tw \<and> wityping \<Gamma> (snd tw))"
  apply (rule ext)
  unfolding wp3_def  using world_seq_exec_bcase_empty world_seq_exec_deterministic by blast

lemma wp3_bcase_others:
  assumes "seq_wt \<Gamma> (Bcase exp ((Others, ss) # choices))" and "nonneg_delay (Bcase exp ((Others, ss) # choices))"
  shows "wp3 \<Gamma> (Bcase exp ((Others, ss) # choices)) Q = wp3 \<Gamma> ss Q"
  apply (rule ext)
  unfolding wp3_def
proof (rule, rule, simp, rule, rule)
  fix x tw'
  have "seq_wt \<Gamma> ss "
    using assms  seq_wt_cases_bcase by auto
  assume *: "wityping \<Gamma> (snd x) \<and> (\<forall>tw'. x, Bcase exp ((Others, ss) # choices) \<Rightarrow>\<^sub>s tw' \<longrightarrow> Q tw')" and "x, ss \<Rightarrow>\<^sub>s tw'"
  thus "Q tw'"
    using world_seq_exec_bcase_others by blast
next
  fix x
  assume *: " wityping \<Gamma> (snd x) \<and> (\<forall>tw'. x, ss \<Rightarrow>\<^sub>s tw' \<longrightarrow> Q tw') "
  hence "wityping \<Gamma> (snd x)" by auto
  { fix tw'
    assume "x, Bcase exp ((Others, ss) # choices) \<Rightarrow>\<^sub>s tw'"
    hence "x, ss \<Rightarrow>\<^sub>s tw'" 
      using bcase_others_tw_elim by blast
    with * have "Q tw'"  
      by blast }
  with `wityping \<Gamma> (snd x)` show " wityping \<Gamma> (snd x) \<and> (\<forall>tw'. x, Bcase exp ((Others, ss) # choices) \<Rightarrow>\<^sub>s tw' \<longrightarrow> Q tw')"
    by auto
qed

lemma wp3_bcase_explicit:
  assumes "seq_wt \<Gamma> (Bcase exp ((Explicit exp', ss) # choices))" and "nonneg_delay (Bcase exp ((Explicit exp', ss) # choices))"
  shows "wp3 \<Gamma> (Bcase exp ((Explicit exp', ss) # choices)) Q = 
  (\<lambda>tw. if eval_world_raw2 tw exp = eval_world_raw2 tw exp' then wp3 \<Gamma> ss Q tw  else wp3 \<Gamma> (Bcase exp choices) Q tw)"
  apply (rule ext)
  unfolding wp3_def
proof (rule)
  fix tw
  assume *: "wityping \<Gamma> (snd tw) \<and> (\<forall>tw'. tw, Bcase exp ((Explicit exp', ss) # choices) \<Rightarrow>\<^sub>s tw' \<longrightarrow> Q tw')"
  hence wt : "wityping \<Gamma> (snd tw)" by auto
  obtain ty where "bexp_wt \<Gamma> exp ty" and " bexp_wt \<Gamma> exp' ty"
    using assms(1) 
    by (smt choices.distinct(1) choices.sel fst_conv list.distinct(1) list.sel(1) seq_stmt.inject(5)
    seq_stmt.simps(15) seq_stmt.simps(23) seq_stmt.simps(29) seq_stmt.simps(33) seq_stmt.simps(35)
    seq_wt.cases)
  have "seq_wt \<Gamma> ss" and "nonneg_delay ss" and "seq_wt \<Gamma> (Bcase exp choices)" and "nonneg_delay (Bcase exp choices)"
    using assms  seq_wt.cases by auto
  have "eval_world_raw2 tw exp = eval_world_raw2 tw exp' \<or> eval_world_raw2 tw exp \<noteq> eval_world_raw2 tw exp'"
    by auto
  moreover
  { assume "eval_world_raw2 tw exp = eval_world_raw2 tw exp'"
    then obtain match where match: "beval_world_raw2 tw exp match \<and> beval_world_raw2 tw exp' match"
      using eval_world_raw_correctness_if[OF _ `wityping \<Gamma> (snd tw)` `bexp_wt \<Gamma> exp ty`]
      eval_world_raw_correctness_if[OF _ `wityping \<Gamma> (snd tw)` `bexp_wt \<Gamma> exp' ty`] 
      by (metis beval_world_raw2_def)
    { fix tw'
      assume "tw, ss \<Rightarrow>\<^sub>s tw'"
      hence  "Q tw'"
        using * world_seq_exec_explicit_match match  by blast 
      moreover have "wityping \<Gamma> (snd tw')"
        using soundness_hoare2[ OF seq_stmt_preserve_wityping_hoare[OF `seq_wt \<Gamma> ss`] `nonneg_delay ss`]
        unfolding seq_hoare_valid2_def using wt `tw, ss\<Rightarrow>\<^sub>s tw'`  by blast
      ultimately have "Q tw' \<and> wityping \<Gamma> (snd tw')"
        by auto }
    hence "if eval_world_raw2 tw exp = eval_world_raw2 tw exp' then wityping \<Gamma> (snd tw) \<and> (\<forall>tw'. tw, ss \<Rightarrow>\<^sub>s tw' \<longrightarrow> Q tw' \<and> wityping \<Gamma> (snd tw'))
          else wityping \<Gamma> (snd tw) \<and> (\<forall>tw'. tw, Bcase exp choices \<Rightarrow>\<^sub>s tw' \<longrightarrow> Q tw' \<and> wityping \<Gamma> (snd tw'))"
      using `eval_world_raw2 tw exp = eval_world_raw2 tw exp'` wt  by simp }
  moreover
  { assume neq: "eval_world_raw2 tw exp \<noteq> eval_world_raw2 tw exp'"
    obtain res1 res2 where "eval_world_raw2 tw exp = res1" and "eval_world_raw2 tw exp' = res2"
      by auto
    hence neq': "beval_world_raw2 tw exp res1 \<and> beval_world_raw2 tw exp' res2 \<and> res1 \<noteq> res2"
      using eval_world_raw_correctness_if[OF `eval_world_raw2 tw exp = res1` `wityping \<Gamma> (snd tw)` `bexp_wt \<Gamma> exp ty`]
      eval_world_raw_correctness_if[OF `eval_world_raw2 tw exp' = res2` `wityping \<Gamma> (snd tw)` `bexp_wt \<Gamma> exp' ty`]
      neq unfolding beval_world_raw2_def by auto
    { fix tw' 
      assume " tw, Bcase exp choices \<Rightarrow>\<^sub>s tw'"
      hence "Q tw'"
        using * neq' world_seq_exec_explicit_no_match by blast
      moreover have "wityping \<Gamma> (snd tw')"
        using soundness_hoare2[ OF seq_stmt_preserve_wityping_hoare[OF `seq_wt \<Gamma> (Bcase exp choices)`] `nonneg_delay (Bcase exp choices)`]
        unfolding seq_hoare_valid2_def using wt `tw, Bcase exp choices \<Rightarrow>\<^sub>s tw'`  by blast
      ultimately have "Q tw' \<and> wityping \<Gamma> (snd tw')"
        by auto }
    hence "if eval_world_raw2 tw exp = eval_world_raw2 tw exp' then wityping \<Gamma> (snd tw) \<and> (\<forall>tw'. tw, ss \<Rightarrow>\<^sub>s tw' \<longrightarrow> Q tw' \<and> wityping \<Gamma> (snd tw'))
          else wityping \<Gamma> (snd tw) \<and> (\<forall>tw'. tw, Bcase exp choices \<Rightarrow>\<^sub>s tw' \<longrightarrow> Q tw' \<and> wityping \<Gamma> (snd tw'))"
      using `eval_world_raw2 tw exp \<noteq> eval_world_raw2 tw exp'` wt  by simp }
  ultimately show "if eval_world_raw2 tw exp = eval_world_raw2 tw exp' then wityping \<Gamma> (snd tw) \<and> (\<forall>tw'. tw, ss \<Rightarrow>\<^sub>s tw' \<longrightarrow> Q tw')
          else wityping \<Gamma> (snd tw) \<and> (\<forall>tw'. tw, Bcase exp choices \<Rightarrow>\<^sub>s tw' \<longrightarrow> Q tw')"
    by auto
next
  fix tw
  assume *: " if eval_world_raw2 tw exp = eval_world_raw2 tw exp' then wityping \<Gamma> (snd tw) \<and> (\<forall>tw'. tw, ss \<Rightarrow>\<^sub>s tw' \<longrightarrow> Q tw')
          else wityping \<Gamma> (snd tw) \<and> (\<forall>tw'. tw, Bcase exp choices \<Rightarrow>\<^sub>s tw' \<longrightarrow> Q tw') "
  hence "wityping \<Gamma> (snd tw)" by presburger
  obtain ty where "bexp_wt \<Gamma> exp ty" and "bexp_wt \<Gamma> exp' ty" using assms(1)  
    by (smt choices.distinct(1) choices.sel fst_conv list.distinct(1) list.sel(1) seq_stmt.inject(5)
    seq_stmt.simps(15) seq_stmt.simps(23) seq_stmt.simps(29) seq_stmt.simps(33) seq_stmt.simps(35)
    seq_wt.cases)
  have "nonneg_delay ss" and "nonneg_delay (Bcase exp choices)"
    using assms(2) by auto
  { fix tw'
    assume "tw, Bcase exp ((Explicit exp', ss) # choices) \<Rightarrow>\<^sub>s tw'"
    hence **: "world_seq_exec_alt tw (Bcase exp ((Explicit exp', ss) # choices)) tw'"
      using assms(2) world_seq_exec_imp_world_seq_exec_alt by blast
    have "Q tw'"
    proof (rule world_seq_exec_alt_cases(6)[OF **])
      fix x
      assume "beval_world_raw2 tw exp x" and "beval_world_raw2 tw exp' x"
      hence "eval_world_raw2 tw exp = x" and "eval_world_raw2 tw exp' = x"
        using eval_world_raw_correctness_only_if[OF _ `wityping \<Gamma> (snd tw)` `bexp_wt \<Gamma> exp ty`]
        using eval_world_raw_correctness_only_if[OF _ `wityping \<Gamma> (snd tw)` `bexp_wt \<Gamma> exp' ty`]
        by (simp add: beval_world_raw2_def)+
      assume "world_seq_exec_alt tw ss tw'"
      hence "tw, ss \<Rightarrow>\<^sub>s tw'"
        using world_seq_exec_alt_imp_world_seq_exec[OF _ `nonneg_delay ss`] by auto
      thus "Q tw'"
        using * 
        by (simp add: \<open>if eval_world_raw2 tw exp = eval_world_raw2 tw exp' then wityping \<Gamma> (snd tw)
        \<and> (\<forall>tw'. tw, ss \<Rightarrow>\<^sub>s tw' \<longrightarrow> Q tw') else wityping \<Gamma> (snd tw) \<and> (\<forall>tw'.
        tw, Bcase exp choices \<Rightarrow>\<^sub>s tw' \<longrightarrow> Q tw')\<close> \<open>eval_world_raw2 tw exp = x\<close>
        \<open>eval_world_raw2 tw exp' = x\<close>)
    next
      fix x x'
      assume "beval_world_raw2 tw exp x" and "beval_world_raw2 tw exp' x'" and "x \<noteq> x'"
      hence "eval_world_raw2 tw exp = x" and "eval_world_raw2 tw exp' = x'"
        using eval_world_raw_correctness_only_if[OF _ `wityping \<Gamma> (snd tw)` `bexp_wt \<Gamma> exp ty`]
        using eval_world_raw_correctness_only_if[OF _ `wityping \<Gamma> (snd tw)` `bexp_wt \<Gamma> exp' ty`]
        using beval_world_raw2_deterministic  by (simp add: beval_world_raw2_def)+
      assume "world_seq_exec_alt tw (Bcase exp choices) tw'"
      hence "tw, Bcase exp choices \<Rightarrow>\<^sub>s tw'"
        using world_seq_exec_alt_imp_world_seq_exec[OF _ `nonneg_delay (Bcase exp choices)`]
        by blast
      thus "Q tw'"
        using * 
        by (simp add: \<open>if eval_world_raw2 tw exp = eval_world_raw2 tw exp' then wityping \<Gamma> (snd tw)
        \<and> (\<forall>tw'. tw, ss \<Rightarrow>\<^sub>s tw' \<longrightarrow> Q tw') else wityping \<Gamma> (snd tw) \<and> (\<forall>tw'.
        tw, Bcase exp choices \<Rightarrow>\<^sub>s tw' \<longrightarrow> Q tw')\<close> \<open>eval_world_raw2 tw exp = x\<close>
        \<open>eval_world_raw2 tw exp' = x'\<close> \<open>x \<noteq> x'\<close>)
    qed }
  thus "wityping \<Gamma> (snd tw) \<and> (\<forall>tw'. tw, Bcase exp ((Explicit exp', ss) # choices) \<Rightarrow>\<^sub>s tw' \<longrightarrow> Q tw')"
    using `wityping \<Gamma> (snd tw)` by auto
qed

lemma wp3_assign_trans:
  assumes "seq_wt \<Gamma> (Bassign_trans sig exp dly)" and " nonneg_delay (Bassign_trans sig exp dly)"
  shows "wp3 \<Gamma> (Bassign_trans sig exp dly) Q = (\<lambda>tw. wityping \<Gamma> (snd tw) \<and> Q(tw[sig, dly :=\<^sub>2 eval_world_raw2 tw exp]))"
  apply (rule ext)
  unfolding wp3_def
proof (rule, rule, simp)
  fix tw
  assume prem: "wityping \<Gamma> (snd tw) \<and> (\<forall>tw'. tw, Bassign_trans sig exp dly \<Rightarrow>\<^sub>s tw' \<longrightarrow> Q tw')"
  obtain tw' where "tw, Bassign_trans sig exp dly \<Rightarrow>\<^sub>s tw'"
    by (metis assms(1) assms(2) beval_world_raw2_def eval_world_raw_correctness_if
    nonneg_delay.simps(4) prem seq_wt_cases(4) world_seq_exec_trans)
  have "beval_world_raw2 tw exp (eval_world_raw2 tw exp)"
    by (metis assms(1) beval_world_raw2_def eval_world_raw_correctness_if prem seq_wt_cases(4))
  thus "Q tw[ sig, dly :=\<^sub>2 eval_world_raw2 tw exp]"
    using prem  by (meson assms(2) nonneg_delay.simps(4) world_seq_exec_trans)
next
  fix tw
  assume *: "wityping \<Gamma> (snd tw) \<and> Q tw[ sig, dly :=\<^sub>2 eval_world_raw2 tw exp] "
  hence wt : "wityping \<Gamma> (snd tw)" by auto
  { fix tw'
    assume "tw, Bassign_trans sig exp dly \<Rightarrow>\<^sub>s tw'"
    hence "Q tw'"
      using *
      by (metis assms(1) assms(2) beval_world_raw2_def eval_world_raw_correctness_only_if
      lift_world_trans_worldline_upd2 nonneg_delay.simps(4) seq_wt_cases(4)) }
  thus "wityping \<Gamma> (snd tw) \<and> (\<forall>tw'. tw, Bassign_trans sig exp dly \<Rightarrow>\<^sub>s tw' \<longrightarrow> Q tw')"
    using wt by auto
qed

lemma wp3_assign_inert:
  assumes "seq_wt \<Gamma> (Bassign_inert sig exp dly)" and " nonneg_delay (Bassign_inert sig exp dly)"
  shows "wp3 \<Gamma> (Bassign_inert sig exp dly) Q = (\<lambda>tw. wityping \<Gamma> (snd tw) \<and> Q(tw\<lbrakk>sig, dly :=\<^sub>2 eval_world_raw2 tw exp\<rbrakk>))"
  apply (rule ext)
  unfolding wp3_def
proof (rule, rule, simp)
  fix tw
  assume prem: "wityping \<Gamma> (snd tw) \<and> (\<forall>tw'. tw, Bassign_inert sig exp dly \<Rightarrow>\<^sub>s tw' \<longrightarrow> Q tw')"
  obtain tw' where "tw, Bassign_inert sig exp dly \<Rightarrow>\<^sub>s tw'"
    by (metis assms(1) assms(2) beval_world_raw2_def eval_world_raw_correctness_if
    nonneg_delay.simps(5) prem seq_wt_cases(5) world_seq_exec_inert)
  have "beval_world_raw2 tw exp (eval_world_raw2 tw exp)"
    by (metis assms(1) beval_world_raw2_def eval_world_raw_correctness_if prem seq_wt_cases(5))
  thus "Q tw\<lbrakk> sig, dly :=\<^sub>2 eval_world_raw2 tw exp\<rbrakk>"
    using prem   by (meson assms(2) nonneg_delay.simps(5) world_seq_exec_inert)
next
  fix tw
  assume *: "wityping \<Gamma> (snd tw) \<and> Q tw\<lbrakk>sig, dly :=\<^sub>2 eval_world_raw2 tw exp\<rbrakk> "
  hence wt : "wityping \<Gamma> (snd tw)" by auto
  { fix tw'
    assume "tw, Bassign_inert sig exp dly \<Rightarrow>\<^sub>s tw'"
    hence "Q tw'"
      using * 
      by (metis assms(1) assms(2) beval_world_raw2_def eval_world_raw_correctness_only_if
      lift_world_inert_worldline_upd2 nonneg_delay.simps(5) seq_wt_cases(5))  }
  thus "wityping \<Gamma> (snd tw) \<and> (\<forall>tw'. tw, Bassign_inert sig exp dly \<Rightarrow>\<^sub>s tw' \<longrightarrow> Q tw')"
    using wt by auto
qed

  
fun wp3_fun :: "'signal tyenv \<Rightarrow> 'signal seq_stmt \<Rightarrow> 'signal assn2 \<Rightarrow> 'signal assn2" where

  "wp3_fun \<Gamma> Bnull Q = (\<lambda>tw. Q tw \<and> wityping \<Gamma> (snd tw))"

| "wp3_fun \<Gamma> (Bassign_trans sig exp dly) Q = (\<lambda>tw. wityping \<Gamma> (snd tw) \<and> Q(tw[sig, dly :=\<^sub>2 eval_world_raw2 tw exp]))"

| "wp3_fun \<Gamma> (Bassign_inert sig exp dly) Q = (\<lambda>tw. wityping \<Gamma> (snd tw) \<and> Q(tw\<lbrakk>sig, dly :=\<^sub>2 eval_world_raw2 tw exp\<rbrakk>))"

| "wp3_fun \<Gamma> (Bcase exp ((Explicit exp', ss) # choices)) Q = 
        (\<lambda>tw. if eval_world_raw2 tw exp = eval_world_raw2 tw exp' then wp3_fun \<Gamma> ss Q tw  else wp3_fun \<Gamma> (Bcase exp choices) Q tw)"

| "wp3_fun \<Gamma> (Bcase exp ((Others, ss) # choices)) Q = wp3_fun \<Gamma> ss Q"

| "wp3_fun \<Gamma> (Bcase exp []) Q = (\<lambda>tw. Q tw \<and> wityping \<Gamma> (snd tw))"

| "wp3_fun \<Gamma> (Bguarded g ss1 ss2) Q = (\<lambda>tw. if eval_world_raw2 tw g = Bv True then  wp3_fun \<Gamma> ss1 Q tw  else  wp3_fun \<Gamma> ss2 Q tw)"

| "wp3_fun \<Gamma> (Bcomp ss1 ss2) Q = wp3_fun \<Gamma> ss1 (wp3_fun \<Gamma> ss2 Q)"

lemma wp3_fun_eq_wp3:
  assumes "seq_wt \<Gamma> ss" and "nonneg_delay ss"
  shows "wp3_fun \<Gamma> ss Q = wp3 \<Gamma> ss Q"
  using assms
  apply (induction ss arbitrary: Q)
  by (auto simp add: wp3_bnull wp3_bcomp wp3_bguarded wp3_assign_trans wp3_assign_inert wp3_bcase_empty wp3_bcase_others wp3_bcase_explicit seq_wt.intros)

lemma wp3_fun_is_pre:
  assumes "seq_wt \<Gamma> ss" and "nonneg_delay ss"
  shows "\<Gamma> \<turnstile> [wp3_fun \<Gamma> ss Q] ss [Q]"
  using assms
proof (induction ss arbitrary:Q)
  case (1 \<Gamma>)
  then show ?case using wp3_bnull 
    by (metis Conseq3 Null3 seq_wt.intros(1) wp3_fun_eq_wp3)
next
  case (2 \<Gamma> s1 s2)
  then show ?case using wp3_fun_eq_wp3 wp3_bcomp 
    by (metis Comp3 nonneg_delay.simps(2) wp3_fun.simps(8))
next
  case (3 \<Gamma> g s1 s2)
  then show ?case using wp3_fun_eq_wp3 wp3_bguarded
    by (smt Conseq3 If3 nonneg_delay.simps(3) seq_wt.intros(3) val.inject(1))
next
  case (4 \<Gamma> exp sig dly)
  then show ?case using wp3_fun_eq_wp3 wp3_assign_trans
    by (smt Conseq3 seq_hoare3.intros(2) wp3_fun.simps(2))
next
  case (5 \<Gamma> exp sig dly)
  then show ?case  using wp3_fun_eq_wp3 wp3_assign_inert
    by (smt Conseq3 seq_hoare3.intros(3) wp3_fun.simps(3))
next
  case (6 \<Gamma> exp ty)
  then show ?case using wp3_fun_eq_wp3 wp3_bcase_empty
    by (smt Bcase_empty_choices3 Conseq3 wp3_fun.simps(6))
next
  case (7 \<Gamma> exp ty ss choices)
  hence "nonneg_delay ss"
    by auto
  hence IH: " \<Gamma> \<turnstile> [wp3_fun \<Gamma> ss Q] ss [Q]"
    using 7(3) by auto
  show ?case
    apply (rule Conseq3[rotated])
      apply (rule Bcase_others3)
      apply (rule IH, simp)
    by (simp add: "7.hyps"(2) \<open>nonneg_delay ss\<close> wp3_fun_eq_wp3)
next
  case (8 \<Gamma> exp ty exp' ss choices) 
  hence " \<Gamma> \<turnstile> [wp3_fun \<Gamma> ss Q] ss [Q]" and  *:  " \<Gamma> \<turnstile> [wp3_fun \<Gamma> (Bcase exp choices) Q] Bcase exp choices [Q]"
    by auto
  hence IH1: "\<Gamma> \<turnstile> [\<lambda>tw. (if eval_world_raw2 tw exp = eval_world_raw2 tw exp' then wp3_fun \<Gamma> ss Q tw else wp3_fun \<Gamma> (Bcase exp choices) Q tw) \<and> eval_world_raw2 tw exp = eval_world_raw2 tw exp'] ss [Q]"
    by (smt Conseq3)
  have  IH2: "\<Gamma> \<turnstile> [\<lambda>tw. (if eval_world_raw2 tw exp = eval_world_raw2 tw exp' then wp3_fun \<Gamma> ss Q tw else wp3_fun \<Gamma> (Bcase exp choices) Q tw) \<and> eval_world_raw2 tw exp \<noteq> eval_world_raw2 tw exp'] Bcase exp choices [Q]"
    using * by (smt Conseq3)
  have swt: "seq_wt \<Gamma> (Bcase exp ((Explicit exp', ss) # choices))"
    using 8  seq_wt.intros(8) by blast
  have nss: "nonneg_delay ss" and not: "nonneg_delay (Bcase exp choices)"
    using 8 by auto
  show ?case
    apply (rule Conseq3[rotated])
      apply (rule Bcase_if3)
    apply (rule IH1, rule IH2, simp)
    unfolding wp3_fun_eq_wp3[OF swt 8(7)] wp3_bcase_explicit[OF swt 8(7)] 
    wp3_fun_eq_wp3[OF 8(3) nss] wp3_fun_eq_wp3[OF 8(4) not] by auto
qed

lemma strengthen_pre_hoare2:
  assumes "\<forall>tw. P' tw \<and> wityping \<Gamma> (snd tw) \<longrightarrow> P tw" and "\<Gamma> \<turnstile> [P] s [Q]"
  shows "\<Gamma> \<turnstile> [P'] s [Q]"
  using assms by (blast intro: Conseq3)

lemma seq_hoare_wt_complete:
  assumes "seq_wt \<Gamma> ss" and "nonneg_delay ss"
  assumes "\<Gamma> \<Turnstile> [P] ss [Q]" 
  shows   "\<Gamma> \<turnstile> [P] ss [Q]"
proof (rule strengthen_pre_hoare2)
  show "\<forall>w. P w \<and> wityping \<Gamma> (snd w) \<longrightarrow> wp3 \<Gamma> ss Q w" using assms
    unfolding seq_hoare_valid2_wt_def wp3_def by auto
  show " \<Gamma> \<turnstile> [wp3 \<Gamma> ss Q] ss [Q]"
    using assms wp3_fun_is_pre wp3_fun_eq_wp3 by fastforce
qed

definition
conc_hoare_valid_wt :: "'signal tyenv \<Rightarrow>'signal assn2 \<Rightarrow> 'signal conc_stmt \<Rightarrow> 'signal assn2 \<Rightarrow> bool" ("(1_) \<Turnstile> \<lbrace>(1_)\<rbrace>/ (_)/ \<lbrace>(1_)\<rbrace>" 50)
where "\<Gamma> \<Turnstile> \<lbrace>P\<rbrace> c \<lbrace>Q\<rbrace> \<longleftrightarrow>  (\<forall>tw tw'.  wityping \<Gamma> (snd tw) \<and> P tw \<and> (tw, c \<Rightarrow>\<^sub>c tw') \<longrightarrow> Q tw')"

lemma conc_hoare_valid_wt_commute:
  assumes "conc_stmt_wf (cs1 || cs2)"
  shows "\<Gamma> \<Turnstile> \<lbrace>P\<rbrace> cs1 || cs2 \<lbrace>Q\<rbrace> \<longleftrightarrow> \<Gamma> \<Turnstile> \<lbrace>P\<rbrace> cs2 || cs1 \<lbrace>Q\<rbrace>"
  unfolding conc_hoare_valid_wt_def using world_conc_exec_commute[OF _ _ assms] 
  by (smt assms parallel_comp_commute world_conc_exec.simps)

inductive
  conc_hoare_wt :: "'signal tyenv \<Rightarrow> 'signal assn2 \<Rightarrow> 'signal conc_stmt \<Rightarrow> 'signal assn2 \<Rightarrow> bool"
  ("(1_) \<turnstile> (\<lbrace>(1_)\<rbrace>/ (_)/ \<lbrace>(1_)\<rbrace>)" 50)
  where
   Single:  "\<Gamma> \<turnstile> [\<lambda>tw. P tw \<and> \<not> disjnt sl (event_of tw)] ss [Q] \<Longrightarrow> \<forall>tw. P tw \<and> disjnt sl (event_of tw) \<longrightarrow> Q tw
    \<Longrightarrow> \<Gamma> \<turnstile> \<lbrace>P\<rbrace> process sl : ss \<lbrace>Q\<rbrace>"
| Parallel:  "\<Gamma> \<turnstile> \<lbrace>P\<rbrace> cs\<^sub>1 \<lbrace>R\<rbrace> \<Longrightarrow> \<Gamma> \<turnstile> \<lbrace>R\<rbrace> cs\<^sub>2 \<lbrace>Q\<rbrace> \<Longrightarrow> conc_stmt_wf (cs\<^sub>1 || cs\<^sub>2) \<Longrightarrow> \<Gamma> \<turnstile> \<lbrace>P\<rbrace> cs\<^sub>1 || cs\<^sub>2 \<lbrace>Q\<rbrace>"
| Parallel2: "\<Gamma> \<turnstile> \<lbrace>P\<rbrace> cs\<^sub>2 \<lbrace>R\<rbrace> \<Longrightarrow> \<Gamma> \<turnstile> \<lbrace>R\<rbrace> cs\<^sub>1 \<lbrace>Q\<rbrace> \<Longrightarrow> conc_stmt_wf (cs\<^sub>1 || cs\<^sub>2) \<Longrightarrow> \<Gamma> \<turnstile> \<lbrace>P\<rbrace> cs\<^sub>1 || cs\<^sub>2 \<lbrace>Q\<rbrace>"
| Conseq': "\<lbrakk>\<forall>w. wityping \<Gamma> (snd w) \<and> P' w \<longrightarrow> P w; \<Gamma> \<turnstile> \<lbrace>P\<rbrace> c \<lbrace>Q\<rbrace>; \<forall>w. Q w \<longrightarrow> Q' w\<rbrakk> \<Longrightarrow> \<Gamma> \<turnstile> \<lbrace>P'\<rbrace> c \<lbrace>Q'\<rbrace>"
| Conj2: "\<Gamma> \<turnstile> \<lbrace>P\<rbrace> s \<lbrace>Q1\<rbrace> \<Longrightarrow> \<Gamma> \<turnstile> \<lbrace>P\<rbrace> s \<lbrace>Q2\<rbrace> \<Longrightarrow> \<Gamma> \<turnstile> \<lbrace>P\<rbrace> s \<lbrace>\<lambda>tw. Q1 tw \<and> Q2 tw\<rbrace>"

inductive_cases conc_hoare_wt_cases : "\<Gamma> \<turnstile> \<lbrace>P\<rbrace> cs \<lbrace>Q\<rbrace>"

lemma parallel_valid:
  assumes "\<Gamma> \<Turnstile> \<lbrace>P\<rbrace> c1 \<lbrace>R\<rbrace>" and "\<Gamma> \<Turnstile> \<lbrace>R\<rbrace> c2 \<lbrace>Q\<rbrace>" and "conc_stmt_wf (c1 || c2)"
  assumes "nonneg_delay_conc (c1 || c2)"
  assumes "conc_wt \<Gamma> (c1 || c2)"
  shows "\<Gamma> \<Turnstile> \<lbrace>P\<rbrace> c1 || c2 \<lbrace>Q\<rbrace>"
  unfolding conc_hoare_valid_wt_def
proof rule+
  fix tw tw':: "nat \<times> 'a worldline_init"
  assume "wityping \<Gamma> (snd tw) \<and> P tw \<and> tw , c1 || c2 \<Rightarrow>\<^sub>c tw'"
  hence "wityping \<Gamma> (snd tw)" and "P tw" and "tw, c1 || c2 \<Rightarrow>\<^sub>c tw'"
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
    using assms(1) `P tw` `wityping \<Gamma> (snd tw)` unfolding conc_hoare_valid_wt_def   by presburger
  have "conc_wt \<Gamma> c1" and "conc_stmt_wf c1" and "nonneg_delay_conc c1"
    using `conc_wt \<Gamma> (c1 || c2)` `conc_stmt_wf (c1 || c2)` assms(4) by auto
  hence "wityping \<Gamma> (snd tw1)"
    using conc_stmt_preserve_wityping_hoare_semantic[OF `conc_wt \<Gamma> c1` `conc_stmt_wf c1`] `tw, c1 \<Rightarrow>\<^sub>c tw1`
    unfolding conc_hoare_valid_def  using \<open>wityping \<Gamma> (snd tw)\<close> by presburger    
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
    using assms(2) `wityping \<Gamma> (snd tw1)` unfolding conc_hoare_valid_wt_def 
    by meson
qed

lemma conseq_valid:
  shows "\<lbrakk>\<forall>w. wityping \<Gamma> (snd w) \<and> P' w \<longrightarrow> P w; \<Gamma> \<Turnstile> \<lbrace>P\<rbrace> c \<lbrace>Q\<rbrace>; \<forall>w. Q w \<longrightarrow> Q' w\<rbrakk> \<Longrightarrow> \<Gamma> \<Turnstile> \<lbrace>P'\<rbrace> c \<lbrace>Q'\<rbrace>"
  unfolding conc_hoare_valid_wt_def by meson

lemma soundness_conc_hoare:
  assumes "\<Gamma> \<turnstile> \<lbrace>P\<rbrace> c \<lbrace>Q\<rbrace>"
  assumes "conc_wt \<Gamma> c" and "conc_stmt_wf c" and "nonneg_delay_conc c"
  shows "\<Gamma> \<Turnstile> \<lbrace>P\<rbrace> c \<lbrace>Q\<rbrace>"
  using assms
proof (induction rule:conc_hoare_wt.induct)
  case (Single \<Gamma> P sl ss Q)
  show ?case 
    unfolding conc_hoare_valid_wt_def
  proof (rule, rule, rule)
    fix tw tw'
    assume *: "wityping \<Gamma> (snd tw) \<and> P tw \<and> tw, process sl : ss \<Rightarrow>\<^sub>c tw'"
    hence 0: "world_conc_exec_alt tw (process sl : ss) tw'"
      using world_conc_exec_eq_world_conc_exec_alt[OF Single(4) Single(5)] by auto
    have "disjnt sl (event_of tw) \<or> \<not> disjnt sl (event_of tw)"
      by auto
    moreover
    { assume "disjnt sl (event_of tw)"
      hence "tw' = tw"
        using 0 
        by (meson \<open>wityping \<Gamma> (snd tw) \<and> P tw \<and> tw , process sl : ss \<Rightarrow>\<^sub>c tw'\<close> world_conc_exec_deterministic world_conc_exec_disjnt)
      hence "Q tw'"
        using Single(2) * `disjnt sl (event_of tw)` by blast }
    moreover
    { assume "\<not> disjnt sl (event_of tw)"
      hence "world_seq_exec_alt tw ss tw'"
        using 0  by (metis "*" Single.prems(3) event_of_def nonneg_delay_conc.simps(1)
        world_seq_exec_imp_world_seq_exec_alt wp_conc_def wp_conc_single wp_def) 
      hence "tw, ss \<Rightarrow>\<^sub>s tw'"
        using world_seq_exec_alt_imp_world_seq_exec Single(5)  nonneg_delay_conc.simps(1) by blast
      moreover have "\<Gamma> \<Turnstile> [\<lambda>tw. P tw \<and> \<not> disjnt sl (event_of tw)] ss [Q]"
        using seq_hoare3_soundness[OF Single(1)] Single(3) Single(5) by auto
      ultimately have "Q tw'"
        using `\<not> disjnt sl (event_of tw)` unfolding seq_hoare_valid2_wt_def  using "*" by blast }
    ultimately show "Q tw'"
      by auto
  qed
next
  case (Parallel \<Gamma> P cs\<^sub>1 R cs\<^sub>2 Q)
  then show ?case using parallel_valid 
    by (metis conc_stmt_wf_def conc_wt_cases(2) distinct_append nonneg_delay_conc.simps(2) signals_from.simps(2))
next
  case (Parallel2 \<Gamma> P cs\<^sub>2 R cs\<^sub>1 Q)
  hence "conc_stmt_wf cs\<^sub>1" and "conc_stmt_wf cs\<^sub>2"
    by (simp add: conc_stmt_wf_def)+
  moreover have "nonneg_delay_conc cs\<^sub>1" and "nonneg_delay_conc cs\<^sub>2"
    using Parallel2 by auto
  ultimately have cs2: " \<Gamma> \<Turnstile> \<lbrace>P\<rbrace> cs\<^sub>2 \<lbrace>R\<rbrace>" and cs1: " \<Gamma> \<Turnstile> \<lbrace>R\<rbrace> cs\<^sub>1 \<lbrace>Q\<rbrace>"
    using Parallel2 by auto
  have "conc_stmt_wf (cs\<^sub>2 || cs\<^sub>1)"
    using Parallel2(3) unfolding conc_stmt_wf_def by auto
  moreover have " nonneg_delay_conc (cs\<^sub>2 || cs\<^sub>1) "
    using Parallel2(8) by auto 
  moreover have " conc_wt \<Gamma> (cs\<^sub>2 || cs\<^sub>1)"
    using Parallel2(6)  conc_wt.intros(2) by blast 
  ultimately have "\<Gamma> \<Turnstile> \<lbrace>P\<rbrace> cs\<^sub>2 || cs\<^sub>1 \<lbrace>Q\<rbrace>"
    using parallel_valid[OF cs2 cs1] by auto
  thus ?case
    using world_conc_exec_commute[OF _ _ Parallel2(3)]  unfolding conc_hoare_valid_wt_def
    by (smt Parallel2.prems(2) parallel_comp_commute' world_conc_exec.intros world_conc_exec_alt_cases(2))
next
  case (Conseq' \<Gamma> P' P c Q Q')
  then show ?case 
    unfolding conc_hoare_valid_wt_def by metis
next
  case (Conj2 \<Gamma> P s Q1 Q2)
  then show ?case by (simp add: conc_hoare_valid_wt_def)
qed

definition wp3_conc :: "'signal tyenv \<Rightarrow> 'signal conc_stmt \<Rightarrow> 'signal assn2 \<Rightarrow> 'signal assn2" where
  "wp3_conc \<Gamma> cs Q = (\<lambda>tw. wityping \<Gamma> (snd tw) \<and> (\<forall>tw'. (tw, cs \<Rightarrow>\<^sub>c tw') \<longrightarrow> Q tw'))"

lemma wp3_conc_single:
  "wp3_conc \<Gamma> (process sl : ss) Q =
  (\<lambda>tw. if disjnt sl (event_of tw) then Q tw \<and> wityping \<Gamma> (snd tw) else wp3 \<Gamma> ss Q tw)"
  apply (rule ext)
  unfolding wp3_conc_def wp3_def
  by (smt conc_cases(1) event_of_def o_apply prod.sel(1) snd_conv world_conc_exec_alt_cases(1)
  world_conc_exec_disjnt world_conc_exec_not_disjnt world_seq_exec.intros)

lemma wp3_conc_single':
  assumes "conc_wt \<Gamma> (process sl : ss)" and "nonneg_delay_conc (process sl : ss) "
  shows "wp3_conc \<Gamma> (process sl : ss) Q =
  (\<lambda>tw. if disjnt sl (event_of tw) then Q tw \<and> wityping \<Gamma> (snd tw) else wp3_fun \<Gamma> ss Q tw)"
  unfolding wp3_conc_single using wp3_fun_eq_wp3 assms  by fastforce

lemma exist_middle_worldline:
  assumes "tw, cs \<Rightarrow>\<^sub>c tw'" and "cs = c1 || c2"
  assumes "conc_stmt_wf cs" and "nonneg_delay_conc cs"
  shows   "\<exists>tw_temp. tw, c1 \<Rightarrow>\<^sub>c tw_temp \<and> tw_temp, c2 \<Rightarrow>\<^sub>c tw'"
  using assms
proof (induction rule: world_conc_exec.induct)
  case (1 tw t \<sigma> \<gamma> \<theta> def \<tau> c \<tau>' tw')
  then obtain \<tau>_temp where \<tau>_temp: " t , \<sigma> , \<gamma> , \<theta>, def  \<turnstile> <c1 , \<tau>> \<longrightarrow>\<^sub>c \<tau>_temp"
    by auto
  then obtain tw_temp where "tw, c1 \<Rightarrow>\<^sub>c tw_temp" and "tw_temp = worldline2 t \<sigma> \<theta> def \<tau>_temp"
    using 1  using world_conc_exec.intros by blast
  have *: "t , \<sigma> , \<gamma> , \<theta>, def  \<turnstile> <c1 || c2, \<tau>> \<longrightarrow>\<^sub>c \<tau>'"
    using 1 by auto
  hence 2: "t , \<sigma> , \<gamma> , \<theta>, def  \<turnstile> <c2 , \<tau>_temp> \<longrightarrow>\<^sub>c \<tau>'" 
    using b_conc_exec_sequential[OF _ * \<tau>_temp] 1 by auto
  have "context_invariant t \<sigma> \<gamma> \<theta> def \<tau>"
    using worldline2_constructible 1  by blast
  hence "context_invariant t \<sigma> \<gamma> \<theta> def \<tau>_temp"
    using \<tau>_temp b_conc_exec_preserves_context_invariant 
    using "1.prems"(1) "1.prems"(3) nonneg_delay_conc.simps(2) by blast
  have ns: " \<forall>s. non_stuttering (to_trans_raw_sig \<tau>) \<sigma> s"
    using "1.hyps"(1) destruct_worldline_ensure_non_stuttering by blast
  have "\<And>n. n \<le> t \<Longrightarrow> \<tau> n = 0"
    using `context_invariant t \<sigma> \<gamma> \<theta> def \<tau>` unfolding context_invariant_def by auto
  hence "\<forall>s. non_stuttering (to_trans_raw_sig \<tau>_temp) \<sigma> s"
    using b_conc_exec_preserves_non_stuttering[OF \<tau>_temp _ _ ] ns 1(5-6) `c = c1 || c2`
    by (simp add: conc_stmt_wf_def)
  moreover have " \<forall>s. non_stuttering (to_trans_raw_sig \<theta>) def s"
    using "1.hyps"(1) destruct_worldline_ensure_non_stuttering_hist_raw by blast
  ultimately have "destruct_worldline tw_temp = (t, \<sigma>, \<gamma>, \<theta>, def, \<tau>_temp)"
    using destruct_worldline_correctness2 
    by (simp add: \<open>context_invariant t \<sigma> \<gamma> \<theta> def \<tau>_temp\<close> \<open>tw_temp = worldline2 t \<sigma> \<theta> def \<tau>_temp\<close>
    destruct_worldline_correctness3)
  hence "tw_temp, c2 \<Rightarrow>\<^sub>c tw'"
    using 2 1(3)  using world_conc_exec.intros by blast
  thus ?case
    by (meson \<open>tw , c1 \<Rightarrow>\<^sub>c tw_temp\<close>)
qed

lemma exist_middle_worldline': 
  assumes "conc_stmt_wf (c1 || c2)" and "nonneg_delay_conc (c1 || c2)"
  shows   "tw, c1 || c2 \<Rightarrow>\<^sub>c tw' \<longleftrightarrow> (\<exists>tw_temp. tw, c1 \<Rightarrow>\<^sub>c tw_temp \<and> tw_temp, c2 \<Rightarrow>\<^sub>c tw')"
  using exist_middle_worldline[OF _ _ assms]
  by (smt assms(1) assms(2) conc_stmt_wf_def distinct_append nonneg_delay_conc.simps(2)
  signals_from.simps(2) world_conc_exec_alt.intros(3) world_conc_exec_alt_imp_world_conc_exec
  world_conc_exec_imp_world_conc_exec_alt)

lemma wp3_conc_parallel:
  assumes "conc_stmt_wf (cs1 || cs2)" and "nonneg_delay_conc (cs1 || cs2)"
  assumes "conc_wt \<Gamma> (cs1 || cs2)"
  shows "wp3_conc \<Gamma> (cs1 || cs2) Q =  wp3_conc \<Gamma> cs1 (wp3_conc \<Gamma> cs2 Q)"
proof (rule ext, rule)
  fix x
  have "conc_stmt_wf cs1" and "conc_stmt_wf cs2"
    using assms  by (simp add: conc_stmt_wf_def)+
  have "nonneg_delay_conc cs1" and "nonneg_delay_conc cs2"
    using assms by auto
  assume "wp3_conc \<Gamma> (cs1 || cs2) Q x "
  hence "(\<forall>tw'. x , cs1 || cs2 \<Rightarrow>\<^sub>c tw' \<longrightarrow> Q tw')" and "wityping \<Gamma> (snd x)"
    unfolding wp3_conc_def by auto  
  then show " wp3_conc \<Gamma> cs1 (wp3_conc \<Gamma> cs2 Q) x"
    unfolding wp3_conc_def sym[OF world_conc_exec_eq_world_conc_exec_alt[OF assms(1-2)]]
    sym[OF world_conc_exec_eq_world_conc_exec_alt[OF `conc_stmt_wf cs1` `nonneg_delay_conc cs1`]]
    sym[OF world_conc_exec_eq_world_conc_exec_alt[OF `conc_stmt_wf cs2` `nonneg_delay_conc cs2`]]
  proof (intro conjI, simp, intro allI, intro impI)
    fix tw'
    assume "\<forall>tw'. world_conc_exec_alt x (cs1 || cs2) tw' \<longrightarrow> Q tw'"
    assume "wityping \<Gamma> (snd x)"
    assume " world_conc_exec_alt x cs1 tw'"
    hence "x, cs1 \<Rightarrow>\<^sub>c tw'"
      using world_conc_exec_alt_imp_world_conc_exec[OF _ `conc_stmt_wf cs1` `nonneg_delay_conc cs1`]
      by auto
    moreover have "conc_wt \<Gamma> cs1"
      using assms(3) by auto
    hence "wityping \<Gamma> (snd tw')"
      using conc_stmt_preserve_wityping_hoare_semantic[OF `conc_wt \<Gamma> cs1` `conc_stmt_wf cs1` `nonneg_delay_conc cs1`]
      unfolding conc_hoare_valid_def using `wityping \<Gamma> (snd x)` `x, cs1 \<Rightarrow>\<^sub>c tw'`  by meson
    moreover have "(\<forall>tw'a. world_conc_exec_alt tw' cs2 tw'a \<longrightarrow> Q tw'a)"
      using \<open>\<forall>tw'. world_conc_exec_alt x (cs1 || cs2) tw' \<longrightarrow> Q tw'\<close> \<open>world_conc_exec_alt x cs1 tw'\<close> world_conc_exec_alt.intros(3) by blast
    ultimately show "wityping \<Gamma> (snd tw') \<and> (\<forall>tw'a. world_conc_exec_alt tw' cs2 tw'a \<longrightarrow> Q tw'a)"
      by auto
  qed
next
  fix x
  have "conc_stmt_wf cs1" and "conc_stmt_wf cs2"
    using assms  by (simp add: conc_stmt_wf_def)+
  have "nonneg_delay_conc cs1" and "nonneg_delay_conc cs2"
    using assms by auto
  assume "wp3_conc \<Gamma> cs1 (wp3_conc \<Gamma> cs2 Q) x"
  hence "\<forall>tw tw'. x , cs1 \<Rightarrow>\<^sub>c tw \<and> tw , cs2 \<Rightarrow>\<^sub>c tw' \<longrightarrow> Q tw'" and "wityping \<Gamma> (snd x)"
    unfolding wp3_conc_def by meson+
  thus "wp3_conc \<Gamma> (cs1 || cs2) Q x"
    unfolding wp3_conc_def sym[OF world_conc_exec_eq_world_conc_exec_alt[OF assms(1-2)]]
  proof (intro conjI, simp, intro allI, intro impI)
    fix tw'
    assume "\<forall>tw tw'. x , cs1 \<Rightarrow>\<^sub>c tw \<and> tw , cs2 \<Rightarrow>\<^sub>c tw' \<longrightarrow> Q tw'"
    assume " wityping \<Gamma> (snd x)"
    assume "world_conc_exec_alt x (cs1 || cs2) tw'" 
    hence "x, (cs1 || cs2) \<Rightarrow>\<^sub>c tw'"
      using world_conc_exec_alt_imp_world_conc_exec[OF _ `conc_stmt_wf (cs1 || cs2)` `nonneg_delay_conc (cs1 || cs2)`]
      by auto
    obtain tw_temp where "x, cs1 \<Rightarrow>\<^sub>c tw_temp \<and> tw_temp, cs2 \<Rightarrow>\<^sub>c tw'"
      using exist_middle_worldline  by (metis \<open>x , cs1 || cs2 \<Rightarrow>\<^sub>c tw'\<close> assms(1) assms(2))
    thus "Q tw'"
      by (simp add: \<open>\<forall>tw tw'. x , cs1 \<Rightarrow>\<^sub>c tw \<and> tw , cs2 \<Rightarrow>\<^sub>c tw' \<longrightarrow> Q tw'\<close>)
  qed
qed

lemma wp3_conc_parallel2:
  assumes "conc_stmt_wf (cs1 || cs2)" and "nonneg_delay_conc (cs1 || cs2)"
  assumes "conc_wt \<Gamma> (cs1 || cs2)"
  shows "wp3_conc \<Gamma> (cs1 || cs2) Q =  wp3_conc \<Gamma> cs2 (wp3_conc \<Gamma> cs1 Q)"
proof (rule ext, rule)
  fix x
  have "conc_stmt_wf cs1" and "conc_stmt_wf cs2"
    using assms  by (simp add: conc_stmt_wf_def)+
  have "nonneg_delay_conc cs1" and "nonneg_delay_conc cs2"
    using assms by auto
  assume "wp3_conc \<Gamma> (cs1 || cs2) Q x"
  hence "\<forall>tw'. x , cs1 || cs2 \<Rightarrow>\<^sub>c tw' \<longrightarrow> Q tw'" and "wityping \<Gamma> (snd x)"
    unfolding wp3_conc_def by auto
  thus" wp3_conc \<Gamma> cs2 (wp3_conc \<Gamma> cs1 Q) x"
    unfolding wp3_conc_def sym[OF world_conc_exec_eq_world_conc_exec_alt[OF assms(1-2)]]
    sym[OF world_conc_exec_eq_world_conc_exec_alt[OF `conc_stmt_wf cs1` `nonneg_delay_conc cs1`]]
    sym[OF world_conc_exec_eq_world_conc_exec_alt[OF `conc_stmt_wf cs2` `nonneg_delay_conc cs2`]]
  proof (intro conjI, simp, intro allI, intro impI)
    fix tw'
    have "conc_stmt_wf (cs2 || cs1)" and "nonneg_delay_conc (cs2 || cs1)"
      using `conc_stmt_wf (cs1 || cs2)` `nonneg_delay_conc (cs1 || cs2)` unfolding conc_stmt_wf_def by  auto
    assume "\<forall>tw'. world_conc_exec_alt x (cs1 || cs2) tw' \<longrightarrow> Q tw'"
    hence  "\<forall>tw'. world_conc_exec_alt x (cs2 || cs1) tw' \<longrightarrow> Q tw'"
      using  
      world_conc_exec_alt_imp_world_conc_exec[OF _ `conc_stmt_wf (cs1 || cs2)` `nonneg_delay_conc (cs1 || cs2)`]
      world_conc_exec_imp_world_conc_exec_alt[OF _ `conc_stmt_wf (cs2 || cs1)` `nonneg_delay_conc (cs2 || cs1)`]
      by (metis \<open>\<And>tw. world_conc_exec tw cs1 = world_conc_exec_alt tw cs1\<close> \<open>\<And>tw. world_conc_exec tw
      cs2 = world_conc_exec_alt tw cs2\<close> \<open>conc_stmt_wf (cs2 || cs1)\<close> \<open>nonneg_delay_conc (cs2 || cs1)\<close>
      exist_middle_worldline world_conc_exec_alt.intros(4) world_conc_exec_alt_imp_world_conc_exec)
    assume "wityping \<Gamma> (snd x)"
    assume " world_conc_exec_alt x cs2 tw'"
    hence "x, cs2 \<Rightarrow>\<^sub>c tw'"
      using world_conc_exec_alt_imp_world_conc_exec[OF _ `conc_stmt_wf cs2` `nonneg_delay_conc cs2`]
      by auto
    moreover have "conc_wt \<Gamma> cs2"
      using assms(3) by auto
    hence "wityping \<Gamma> (snd tw')"
      using conc_stmt_preserve_wityping_hoare_semantic[OF `conc_wt \<Gamma> cs2` `conc_stmt_wf cs2` `nonneg_delay_conc cs2`]
      unfolding conc_hoare_valid_def using `wityping \<Gamma> (snd x)` `x, cs2 \<Rightarrow>\<^sub>c tw'`  by meson
    moreover have "(\<forall>tw'a. world_conc_exec_alt tw' cs1 tw'a \<longrightarrow> Q tw'a)"
      using \<open>\<forall>tw'. world_conc_exec_alt x (cs2 || cs1) tw' \<longrightarrow> Q tw'\<close> \<open>world_conc_exec_alt x cs2 tw'\<close> world_conc_exec_alt.intros(3) 
      by blast
    ultimately show "wityping \<Gamma> (snd tw') \<and> (\<forall>tw'a. world_conc_exec_alt tw' cs1 tw'a \<longrightarrow> Q tw'a)"
      by auto
  qed
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
  assume "wp3_conc \<Gamma> cs2 (wp3_conc \<Gamma> cs1 Q) x"
  hence "\<forall>tw tw'. x , cs2 \<Rightarrow>\<^sub>c tw \<and> tw , cs1 \<Rightarrow>\<^sub>c tw' \<longrightarrow> Q tw'" and "wityping \<Gamma> (snd x)"
    unfolding wp3_conc_def  by metis+
  hence "wp3_conc \<Gamma> (cs2 || cs1) Q x"
    unfolding wp3_conc_def
    using sym[OF world_conc_exec_eq_world_conc_exec_alt[OF `conc_stmt_wf (cs2 || cs1)` `nonneg_delay_conc (cs2 || cs1)`]]
    by (metis \<open>conc_stmt_wf (cs2 || cs1)\<close> \<open>nonneg_delay_conc (cs2 || cs1)\<close> wp_conc_def wp_conc_parallel)
  thus "wp3_conc \<Gamma> (cs1 || cs2) Q x"
    unfolding wp3_conc_def by (smt assms(1) parallel_comp_commute' world_conc_exec.intros world_conc_exec_cases)
qed
  
lemma wp3_conc_is_pre:
  assumes "conc_stmt_wf cs" and "nonneg_delay_conc cs"
  assumes "conc_wt \<Gamma> cs"
  shows "\<Gamma> \<turnstile> \<lbrace>wp3_conc \<Gamma> cs Q\<rbrace> cs \<lbrace>Q\<rbrace>"
  using assms
proof (induction cs arbitrary:Q)
  case (Bpar cs1 cs2)
  hence "conc_stmt_wf cs1" and "conc_stmt_wf cs2" and "nonneg_delay_conc cs1" and "nonneg_delay_conc cs2"
    by auto
  hence "\<And>Q.  \<Gamma> \<turnstile> \<lbrace>wp3_conc \<Gamma> cs1 Q\<rbrace> cs1 \<lbrace>Q\<rbrace>" and "\<And>Q.  \<Gamma> \<turnstile> \<lbrace>wp3_conc \<Gamma> cs2 Q\<rbrace> cs2 \<lbrace>Q\<rbrace>"
    using Bpar(1-2)  Bpar.prems(3) by blast+
  then show ?case
    unfolding wp3_conc_parallel[OF Bpar(3-4)]
    by (metis Bpar.prems(1) Bpar.prems(3) \<open>\<And>\<Gamma> Q. conc_wt \<Gamma> (cs1 || cs2) \<Longrightarrow> wp3_conc \<Gamma> (cs1 || cs2) Q = wp3_conc \<Gamma> cs1 (wp3_conc \<Gamma> cs2 Q)\<close> conc_hoare_wt.Parallel)
next
  case (Bsingle sl ss)
  hence "nonneg_delay ss"
    by auto
  then show ?case  unfolding wp3_conc_single
    apply (intro Single)
    by (smt Bsingle.prems(3) Conseq3 conc_wt_cases(1) wp3_fun_eq_wp3 wp3_fun_is_pre) auto
qed

lemma wp3_conc_is_pre_valid:
  assumes "conc_stmt_wf cs" and "nonneg_delay_conc cs"
  assumes "conc_wt \<Gamma> cs"
  shows "\<Gamma> \<Turnstile> \<lbrace>wp3_conc \<Gamma> cs Q\<rbrace> cs \<lbrace>Q\<rbrace>"
  using assms  by (simp add: VHDL_Hoare_Typed.soundness_conc_hoare wp3_conc_is_pre)

definition
sim_hoare_valid_wt :: "'signal tyenv \<Rightarrow> 'signal assn2 \<Rightarrow> 'signal conc_stmt \<Rightarrow> 'signal assn2 \<Rightarrow> bool" ("(1_) \<Turnstile>\<^sub>s \<lbrace>(1_)\<rbrace>/ (_)/ \<lbrace>(1_)\<rbrace>" 50)
where "\<Gamma> \<Turnstile>\<^sub>s \<lbrace>P\<rbrace> cs \<lbrace>Q\<rbrace> \<longleftrightarrow> (\<forall>tw T tw'. wityping \<Gamma> (snd tw) \<and> P tw \<and> (tw, T, cs \<Rightarrow>\<^sub>S tw') \<longrightarrow> Q tw')"

lemma true_program_true:
  \<open>\<Gamma> \<Turnstile>\<^sub>s \<lbrace>\<lambda>tw. True\<rbrace> cs \<lbrace>\<lambda>tw. True\<rbrace>\<close> 
  unfolding sim_hoare_valid_wt_def by auto

inductive
  sim_hoare :: "'signal tyenv \<Rightarrow> 'signal assn2 \<Rightarrow> 'signal conc_stmt \<Rightarrow> 'signal assn2 \<Rightarrow> bool"
  ("(1_) \<turnstile>\<^sub>s (\<lbrace>(1_)\<rbrace>/ (_)/ \<lbrace>(1_)\<rbrace>)" 50)
  where
While_Suc: "\<Gamma> \<turnstile> \<lbrace>\<lambda>tw. P tw\<rbrace> cs \<lbrace> \<lambda>tw. P (fst tw + 1, snd tw)\<rbrace>  \<Longrightarrow> \<Gamma> \<turnstile>\<^sub>s \<lbrace>P\<rbrace> cs \<lbrace>P\<rbrace>" |
Conseq_sim: "\<forall>tw. wityping \<Gamma> (snd tw) \<and> P' tw \<longrightarrow> P tw \<Longrightarrow> \<Gamma> \<turnstile>\<^sub>s \<lbrace>P\<rbrace> cs \<lbrace>Q\<rbrace> \<Longrightarrow> \<forall>tw. Q tw \<longrightarrow> Q' tw \<Longrightarrow> \<Gamma> \<turnstile>\<^sub>s \<lbrace>P'\<rbrace> cs \<lbrace>Q'\<rbrace>" |
Conj_sim : "\<Gamma> \<turnstile>\<^sub>s \<lbrace>P\<rbrace> cs \<lbrace>Q1\<rbrace> \<Longrightarrow> \<Gamma> \<turnstile>\<^sub>s \<lbrace>P\<rbrace> cs \<lbrace>Q2\<rbrace> \<Longrightarrow> \<Gamma> \<turnstile>\<^sub>s \<lbrace>P\<rbrace> cs \<lbrace>\<lambda>tw. Q1 tw \<and> Q2 tw\<rbrace>"

inductive_cases sim_hoare_cases: "\<Gamma> \<turnstile>\<^sub>s \<lbrace>P\<rbrace> cs \<lbrace>Q\<rbrace>"

lemma while_soundness:
  assumes "\<Gamma> \<Turnstile> \<lbrace>P\<rbrace> cs \<lbrace>\<lambda>tw. P (fst tw + 1, snd tw)\<rbrace>"
  assumes "tw, T, cs \<Rightarrow>\<^sub>S tw'"
  assumes "P tw"      
  assumes "nonneg_delay_conc cs" and "conc_stmt_wf cs" and "conc_wt \<Gamma> cs" and "wityping \<Gamma> (snd tw)"
  shows   "P tw'"
proof -
  have " world_sim_fin2 tw T cs tw'"
    using only_context_matters_for_sim_fin2[OF assms(2) assms(4-5)] world_sim_fin_semi_equivalent[OF assms(2) _ assms(4-5)] 
    by auto
  hence "world_sim_fin2_alt tw T cs tw'"
    unfolding world_sim_fin2_eq_world_sim_fin2_alt[OF assms(5) assms(4), THEN sym] by auto
  thus ?thesis
    using assms(1) assms(3-7)
  proof (induction rule: world_sim_fin2_alt.inducts)
    case (1 tw T cs tw2 tw3)
    hence "tw, cs \<Rightarrow>\<^sub>c tw2"
      unfolding world_conc_exec_eq_world_conc_exec_alt[OF ` conc_stmt_wf cs` `nonneg_delay_conc cs`]
      by auto
    hence "P (get_time tw2 + 1, snd tw2)"
      using `\<Gamma> \<Turnstile> \<lbrace>\<lambda>tw. P tw\<rbrace> cs \<lbrace>\<lambda>tw. P (get_time tw + 1, snd tw)\<rbrace>` `fst tw < T` `P tw` `wityping \<Gamma> (snd tw)`
      unfolding conc_hoare_valid_wt_def  by presburger
    moreover have "wityping \<Gamma> (snd (get_time tw2 + 1, snd tw2))"
      using `wityping \<Gamma> (snd tw)` conc_stmt_preserve_wityping_hoare_semantic[OF `conc_wt \<Gamma> cs` `conc_stmt_wf cs` `nonneg_delay_conc cs`]
      unfolding conc_hoare_valid_def using `tw, cs\<Rightarrow>\<^sub>c tw2`  by (metis snd_conv)
    ultimately show ?case 
      using 1(4)[OF `\<Gamma> \<Turnstile> \<lbrace>\<lambda>tw. P tw\<rbrace> cs \<lbrace>\<lambda>tw. P (get_time tw + 1, snd tw)\<rbrace>`]
      using "1.prems"(3) "1.prems"(4) ` conc_wt \<Gamma> cs` by auto
  next
    case (2 tw T cs)
    then show ?case by auto
  qed
qed

lemma conc_sim_soundness:
  assumes "\<Gamma> \<turnstile>\<^sub>s \<lbrace>P\<rbrace> cs \<lbrace>Q\<rbrace>"
  assumes "nonneg_delay_conc cs" and "conc_stmt_wf cs" and "conc_wt \<Gamma> cs"
  shows "\<Gamma> \<Turnstile>\<^sub>s \<lbrace>P\<rbrace> cs \<lbrace>Q\<rbrace>"
  using assms
proof (induction rule:sim_hoare.induct)
  case (While_Suc \<Gamma> P cs)
  hence " \<Gamma> \<Turnstile> \<lbrace>\<lambda>tw. P tw\<rbrace> cs \<lbrace>\<lambda>tw. P (fst tw + 1, snd tw)\<rbrace>"
    using soundness_conc_hoare[OF While_Suc(1)]  by auto
  then show ?case 
    unfolding sim_hoare_valid_wt_def using while_soundness4[OF _ _ _ While_Suc(2-3)]
    by (metis (mono_tags, lifting) While_Suc.prems(1) While_Suc.prems(2) While_Suc.prems(3) while_soundness)
next
  case (Conseq_sim \<Gamma> P' P cs Q Q')
  then show ?case 
    by (smt sim_hoare_valid_wt_def)
next
  case (Conj_sim \<Gamma> P cs Q1 Q2)
  then show ?case 
    by (simp add: sim_hoare_valid_wt_def)
qed

lemma While_Suc':
  assumes "nonneg_delay_conc cs" and "conc_stmt_wf cs" and "conc_wt \<Gamma> cs"
  shows   "\<Gamma> \<Turnstile> \<lbrace>\<lambda>tw. P tw\<rbrace> cs \<lbrace> \<lambda>tw. P (fst tw + 1, snd tw)\<rbrace>  \<Longrightarrow> \<Gamma> \<Turnstile>\<^sub>s \<lbrace>P\<rbrace> cs \<lbrace>P\<rbrace>"
  using While_Suc conc_sim_soundness[OF _ assms] soundness_conc_hoare[OF _ assms(3) assms(2) assms(1)]
  using assms(1) assms(2) assms(3) sim_hoare_valid_wt_def while_soundness by fastforce

lemma conseq_sim_valid:
  "\<forall>tw. wityping \<Gamma> (snd tw) \<and> P' tw \<longrightarrow> P tw \<Longrightarrow> \<Gamma> \<Turnstile>\<^sub>s \<lbrace>P\<rbrace> cs \<lbrace>Q\<rbrace> \<Longrightarrow> \<forall>tw. Q tw \<longrightarrow> Q' tw \<Longrightarrow> \<Gamma> \<Turnstile>\<^sub>s \<lbrace>P'\<rbrace> cs \<lbrace>Q'\<rbrace>"
  unfolding sim_hoare_valid_wt_def by blast

lemma conc_wt_progress_world_sim:
  assumes "fst tw \<le> T" 
  assumes \<open>conc_wt \<Gamma> cs\<close>
  assumes \<open>nonneg_delay_conc cs\<close>
  assumes \<open>wityping \<Gamma> (snd tw)\<close>
  assumes \<open>conc_stmt_wf cs\<close>
  shows   "\<exists>tw'. tw, T, cs \<Rightarrow>\<^sub>S tw'"
proof -
  obtain t \<sigma> \<gamma> \<theta> def \<tau> where "destruct_worldline tw = (t, \<sigma>, \<gamma>, \<theta>, def, \<tau>)"
    using destruct_worldline_exist by blast
  hence "ttyping \<Gamma> \<tau>"
    using `wityping \<Gamma> (snd tw)` wityping_ensure_ttyping2 
    by (metis (no_types, lifting) destruct_worldline_def snd_conv)
  have "ttyping \<Gamma> \<theta>"
    using wityping_ensure_ttyping 
    by (smt Pair_inject \<open>destruct_worldline tw = (t, \<sigma>, \<gamma>, \<theta>, def, \<tau>)\<close> assms(4) destruct_worldline_def)
  have "styping \<Gamma> \<sigma>"
    by (metis (no_types, lifting) Pair_inject \<open>destruct_worldline tw = (t, \<sigma>, \<gamma>, \<theta>, def, \<tau>)\<close>
    assms(4) destruct_worldline_def styping_def wityping_def wtyping_def)
  have "styping \<Gamma> def"
    by (metis (mono_tags, lifting) \<open>destruct_worldline tw = (t, \<sigma>, \<gamma>, \<theta>, def, \<tau>)\<close> assms(4) destruct_worldline_def fst_conv snd_conv wityping_def)
  obtain t' \<sigma>' \<theta>' \<tau>' where " T, t, \<sigma>, \<gamma>, \<theta>, def \<turnstile> <cs, \<tau>> \<leadsto>s (t', \<sigma>', \<theta>', \<tau>')"
    using conc_wt_simulation_progress[OF assms(2-3) `ttyping \<Gamma> \<tau>` `ttyping \<Gamma> \<theta>` `styping \<Gamma> \<sigma>` `styping \<Gamma> def`]
    by (metis (full_types) \<open>destruct_worldline tw = (t, \<sigma>, \<gamma>, \<theta>, def, \<tau>)\<close> assms(1) fst_conv fst_destruct_worldline prod_cases4)
  hence "\<exists>tw'. world_sim_fin2 tw T cs tw'"
    using \<open>destruct_worldline tw = (t, \<sigma>, \<gamma>, \<theta>, def, \<tau>)\<close> world_sim_fin2.intros by blast
  thus ?thesis
    using world_sim_fin2_imp_fin  using assms(3) assms(5) by blast
qed

lemma simulation_semi_complete:
  assumes \<open>\<Gamma> \<Turnstile>\<^sub>s \<lbrace>P\<rbrace> cs \<lbrace>P\<rbrace>\<close>
  assumes "nonneg_delay_conc cs" and "conc_stmt_wf cs" and "conc_wt \<Gamma> cs" 
  shows   \<open>\<Gamma> \<Turnstile> \<lbrace>P\<rbrace> cs \<lbrace>\<lambda>tw. P (fst tw + 1, snd tw)\<rbrace>\<close>
proof -
  have *: "\<And>tw T tw'. wityping \<Gamma> (snd tw) \<Longrightarrow> P tw \<Longrightarrow>  tw, T, cs \<Rightarrow>\<^sub>S tw' \<Longrightarrow> P tw'"
    using assms(1) unfolding sim_hoare_valid_wt_def by auto
  { fix tw tw'
    assume "wityping \<Gamma> (snd tw)" and "P tw"
    assume " tw , cs \<Rightarrow>\<^sub>c tw'"
    obtain tw_fin where "tw, fst tw + 1, cs \<Rightarrow>\<^sub>S tw_fin"
      using conc_wt_progress_world_sim 
      by (metis \<open>wityping \<Gamma> (snd tw)\<close> add.commute assms(2) assms(3) assms(4) le_add2)
    hence "P tw_fin"
      using *[OF `wityping \<Gamma> (snd tw)` `P tw`] by blast
    have "tw_fin = (fst tw + 1, snd tw_fin)"
      using \<open>tw, get_time tw + 1, cs \<Rightarrow>\<^sub>S tw_fin\<close> world_maxtime_lt_fst_tres by fastforce
    have "world_sim_fin2 tw (fst tw + 1) cs tw_fin"
      using \<open>tw, get_time tw + 1, cs \<Rightarrow>\<^sub>S tw_fin\<close> assms(2) assms(3) world_sim_fin_imp_fin2 by blast
    hence "world_sim_fin2_alt tw (fst tw + 1) cs tw_fin"
      by (simp add: assms(2) assms(3) world_sim_fin2_eq_world_sim_fin2_alt)
    then obtain tw2 where "world_conc_exec_alt tw cs tw2" and "world_sim_fin2_alt (fst tw2 + 1, snd tw2) (fst tw + 1) cs tw_fin"
      by (metis (no_types, lifting) less_add_one not_add_less1 world_sim_fin2_alt.simps)
    hence " tw , cs \<Rightarrow>\<^sub>c tw2"
      using assms(2) assms(3) world_conc_exec_alt_imp_world_conc_exec by blast
    have "tw_fin = (fst tw2 + 1, snd tw2)"
      by (metis (no_types, lifting) One_nat_def \<open>tw , cs \<Rightarrow>\<^sub>c tw2\<close> \<open>world_sim_fin2_alt (get_time tw2
      + 1, snd tw2) (get_time tw + 1) cs tw_fin\<close> fst_conv fst_world_conc_exec group_cancel.add1
      not_add_less1 plus_1_eq_Suc world_sim_fin2_alt.cases)
    hence "P (get_time tw' + 1, snd tw')"
      by (metis \<open>P tw_fin\<close> \<open>tw , cs \<Rightarrow>\<^sub>c tw'\<close> \<open>tw , cs \<Rightarrow>\<^sub>c tw2\<close> world_conc_exec_deterministic) }
  thus ?thesis
    unfolding conc_hoare_valid_wt_def by metis
qed

lemma sim_hoare_valid_wt_parallel_commute:
  assumes "conc_stmt_wf (cs1 || cs2)"
  shows " \<Gamma> \<Turnstile>\<^sub>s \<lbrace>P\<rbrace> (cs1 || cs2) \<lbrace>Q\<rbrace> \<longleftrightarrow> \<Gamma> \<Turnstile>\<^sub>s \<lbrace>P\<rbrace> (cs2 || cs1) \<lbrace>Q\<rbrace>"
  unfolding sim_hoare_valid_wt_def world_sim_fin_parallel_commute[OF assms]
  by auto

lemma sim_hoare_valid_wt_parallel_distrib:
  assumes "conc_stmt_wf ((cs1 || cs2) || cs3)"
  shows "\<Gamma> \<Turnstile>\<^sub>s \<lbrace>P\<rbrace> (cs1 || cs2) || cs3 \<lbrace>Q\<rbrace> \<longleftrightarrow> \<Gamma> \<Turnstile>\<^sub>s \<lbrace>P\<rbrace> (cs1 || cs3) || (cs2 || cs3) \<lbrace>Q\<rbrace>"
  unfolding sim_hoare_valid_wt_def world_sim_fin_parallel_distrib[OF assms]
  by blast

lemma sim_hoare_valid_wt_parallel_associative:
  assumes "conc_stmt_wf ((cs1 || cs2) || cs3)"  
  shows "\<Gamma> \<Turnstile>\<^sub>s \<lbrace>P\<rbrace> (cs1 || cs2) || cs3 \<lbrace>Q\<rbrace> \<longleftrightarrow> \<Gamma> \<Turnstile>\<^sub>s \<lbrace>P\<rbrace> cs1 || cs2 || cs3 \<lbrace>Q\<rbrace>"
  unfolding sim_hoare_valid_wt_def world_sim_fin_parallel_associative[OF assms]
  by blast

lemma comb_sim_hoare_valid_wt:
  assumes "\<Gamma> \<Turnstile>\<^sub>s \<lbrace>P1\<rbrace> cs \<lbrace>Q1\<rbrace>" and "\<Gamma> \<Turnstile>\<^sub>s \<lbrace>P2\<rbrace> cs \<lbrace>Q2\<rbrace>"
  shows   "\<Gamma> \<Turnstile>\<^sub>s \<lbrace>\<lambda>tw. P1 tw \<and> P2 tw\<rbrace> cs \<lbrace>\<lambda>tw. Q1 tw \<and> Q2 tw\<rbrace>"
  using assms unfolding sim_hoare_valid_wt_def  by blast

inductive
  init_hoare :: "'signal tyenv \<Rightarrow> 'signal assn2 \<Rightarrow> 'signal conc_stmt \<Rightarrow> 'signal assn2 \<Rightarrow> bool"
  ("(1_) \<turnstile>\<^sub>I (\<lbrace>(1_)\<rbrace>/ (_)/ \<lbrace>(1_)\<rbrace>)" 50)
  where
  SingleI:    "\<Gamma> \<turnstile> [P] ss [Q] \<Longrightarrow> \<Gamma> \<turnstile>\<^sub>I \<lbrace>P\<rbrace> process sl : ss \<lbrace>Q\<rbrace>"
| ParallelI:  "\<Gamma> \<turnstile>\<^sub>I \<lbrace>P\<rbrace> cs\<^sub>1 \<lbrace>R\<rbrace> \<Longrightarrow> \<Gamma> \<turnstile>\<^sub>I \<lbrace>R\<rbrace> cs\<^sub>2 \<lbrace>Q\<rbrace> \<Longrightarrow> conc_stmt_wf (cs\<^sub>1 || cs\<^sub>2) \<Longrightarrow> \<Gamma> \<turnstile>\<^sub>I \<lbrace>P\<rbrace> cs\<^sub>1 || cs\<^sub>2 \<lbrace>Q\<rbrace>"
| ParallelI2: "\<Gamma> \<turnstile>\<^sub>I \<lbrace>P\<rbrace> cs\<^sub>2 \<lbrace>R\<rbrace> \<Longrightarrow> \<Gamma> \<turnstile>\<^sub>I \<lbrace>R\<rbrace> cs\<^sub>1 \<lbrace>Q\<rbrace> \<Longrightarrow> conc_stmt_wf (cs\<^sub>1 || cs\<^sub>2) \<Longrightarrow> \<Gamma> \<turnstile>\<^sub>I \<lbrace>P\<rbrace> cs\<^sub>1 || cs\<^sub>2 \<lbrace>Q\<rbrace>"
| ConseqI:    "\<lbrakk>\<forall>w. P' w \<longrightarrow> P w; \<Gamma> \<turnstile>\<^sub>I \<lbrace>P\<rbrace> cs \<lbrace>Q\<rbrace>; \<forall>w. Q w \<longrightarrow> Q' w\<rbrakk> \<Longrightarrow> \<Gamma> \<turnstile>\<^sub>I \<lbrace>P'\<rbrace> cs \<lbrace>Q\<rbrace>"
| ConjI:      "\<Gamma> \<turnstile>\<^sub>I \<lbrace>P\<rbrace> cs \<lbrace>Q1\<rbrace> \<Longrightarrow> \<Gamma> \<turnstile>\<^sub>I \<lbrace>P\<rbrace> cs \<lbrace>Q2\<rbrace> \<Longrightarrow> \<Gamma> \<turnstile>\<^sub>I \<lbrace>P\<rbrace> cs \<lbrace>\<lambda>tw. Q1 tw \<and> Q2 tw\<rbrace>"

definition
  init_hoare_valid_wt :: "'signal tyenv \<Rightarrow> 'signal assn2 \<Rightarrow> 'signal conc_stmt \<Rightarrow> 'signal assn2 \<Rightarrow> bool" ("(1_) \<Turnstile>\<^sub>I \<lbrace>(1_)\<rbrace>/ (_)/ \<lbrace>(1_)\<rbrace>" 50)
  where "\<Gamma> \<Turnstile>\<^sub>I \<lbrace>P\<rbrace> cs \<lbrace>Q\<rbrace> \<longleftrightarrow>  (\<forall>tw tw'.  wityping \<Gamma> (snd tw) \<and> P tw \<and> (tw, cs \<Rightarrow>\<^sub>I tw') \<longrightarrow> Q tw')"

lemma exist_middle_worldline_init:
  assumes "tw, cs \<Rightarrow>\<^sub>I tw'" and "cs = c1 || c2"
  assumes "conc_stmt_wf cs" and "nonneg_delay_conc cs"
  shows   "\<exists>tw_temp. tw, c1 \<Rightarrow>\<^sub>I tw_temp \<and> tw_temp, c2 \<Rightarrow>\<^sub>I tw'"
  using assms
proof (induction rule: world_init_exec.induct)
  case (1 tw t \<sigma> \<gamma> \<theta> def \<tau> cs \<tau>' tw')
  then obtain \<tau>_temp where \<tau>_temp: " init' t  \<sigma>  \<gamma>  \<theta> def c1  \<tau> \<tau>_temp"
    by auto
  then obtain tw_temp where "tw, c1 \<Rightarrow>\<^sub>I tw_temp" and "tw_temp = worldline2 t \<sigma> \<theta> def \<tau>_temp"
    using 1  using world_init_exec.intros by blast
  have *: "init' t  \<sigma>  \<gamma>  \<theta> def  (c1 || c2) \<tau> \<tau>'"
    using 1 by auto
  hence 2: "init' t \<sigma> \<gamma> \<theta> def c2 \<tau>_temp \<tau>'"
    using init'_sequential[OF _ * \<tau>_temp] 1 by auto
  have "context_invariant t \<sigma> \<gamma> \<theta> def \<tau>"
    using worldline2_constructible 1  by blast
  hence "context_invariant t \<sigma> \<gamma> \<theta> def \<tau>_temp"
    using \<tau>_temp init'_preserves_context_invariant 
    using "1.prems"(1) "1.prems"(3) nonneg_delay_conc.simps(2) by blast
  have ns: " \<forall>s. non_stuttering (to_trans_raw_sig \<tau>) \<sigma> s"
    using "1.hyps"(1) destruct_worldline_ensure_non_stuttering by blast
  have "\<And>n. n \<le> t \<Longrightarrow> \<tau> n = 0"
    using `context_invariant t \<sigma> \<gamma> \<theta> def \<tau>` unfolding context_invariant_def by auto
  hence "\<forall>s. non_stuttering (to_trans_raw_sig \<tau>_temp) \<sigma> s"
    using init'_preserves_non_stuttering[OF \<tau>_temp _ _ ] ns 1(5-6) `cs = c1 || c2`
    by (simp add: conc_stmt_wf_def)
  moreover have " \<forall>s. non_stuttering (to_trans_raw_sig \<theta>) def s"
    using "1.hyps"(1) destruct_worldline_ensure_non_stuttering_hist_raw by blast
  ultimately have "destruct_worldline tw_temp = (t, \<sigma>, \<gamma>, \<theta>, def, \<tau>_temp)"
    using destruct_worldline_correctness2 
    by (simp add: \<open>context_invariant t \<sigma> \<gamma> \<theta> def \<tau>_temp\<close> \<open>tw_temp = worldline2 t \<sigma> \<theta> def \<tau>_temp\<close>
    destruct_worldline_correctness3)
  hence "tw_temp, c2 \<Rightarrow>\<^sub>I tw'"
    using 2 1(3)  using world_init_exec.intros by blast
  thus ?case
    by (meson \<open>tw , c1 \<Rightarrow>\<^sub>I tw_temp\<close>)
qed

lemma parallelI_valid:
  assumes "\<Gamma> \<Turnstile>\<^sub>I \<lbrace>P\<rbrace> c1 \<lbrace>R\<rbrace>" and "\<Gamma> \<Turnstile>\<^sub>I \<lbrace>R\<rbrace> c2 \<lbrace>Q\<rbrace>" and "conc_stmt_wf (c1 || c2)"
  assumes "nonneg_delay_conc (c1 || c2)" and "conc_wt \<Gamma> (c1 || c2)"
  shows "\<Gamma> \<Turnstile>\<^sub>I \<lbrace>P\<rbrace> c1 || c2 \<lbrace>Q\<rbrace>"
  unfolding init_hoare_valid_wt_def
proof (rule, rule, rule)
  fix tw tw'
  assume *: "wityping \<Gamma> (snd tw) \<and> P tw \<and> tw , c1 || c2 \<Rightarrow>\<^sub>I tw'"
  then obtain tw_temp where "tw, c1 \<Rightarrow>\<^sub>I tw_temp" and "tw_temp, c2 \<Rightarrow>\<^sub>I tw'"
    using exist_middle_worldline_init[OF _ _ `conc_stmt_wf (c1 || c2)` `nonneg_delay_conc (c1 || c2)`]
    by metis
  hence "R tw_temp"
    using assms(1) *  unfolding init_hoare_valid_wt_def by blast
  have "wityping \<Gamma> (snd tw_temp)"
    using init_preserve_wityping_semantic `conc_wt \<Gamma> (c1 || c2)` `conc_stmt_wf (c1 || c2)` `nonneg_delay_conc (c1 || c2)` *
    `tw, c1 \<Rightarrow>\<^sub>I tw_temp` unfolding init_hoare_valid_def conc_stmt_wf_def 
  proof -
    assume "distinct (signals_from (c1 || c2))"
    then show ?thesis
      by (metis (no_types) "*" \<open>conc_wt \<Gamma> (c1 || c2)\<close> \<open>nonneg_delay_conc (c1 || c2)\<close> \<open>tw , c1 \<Rightarrow>\<^sub>I tw_temp\<close> conc_stmt_wf_def conc_wt_cases(2) distinct_append init_hoare_valid_def init_preserve_wityping_semantic nonneg_delay_conc.simps(2) signals_from.simps(2))
  qed
  thus "Q tw'"
    using assms(2) `R tw_temp` `tw_temp, c2 \<Rightarrow>\<^sub>I tw'` unfolding init_hoare_valid_wt_def by blast
qed
  
lemma soundness_init_hoare:
  assumes "\<Gamma> \<turnstile>\<^sub>I \<lbrace>P\<rbrace> c \<lbrace>Q\<rbrace>"
  assumes "conc_stmt_wf c" and "nonneg_delay_conc c" and "conc_wt \<Gamma> c"
  shows   "\<Gamma> \<Turnstile>\<^sub>I \<lbrace>P\<rbrace> c \<lbrace>Q\<rbrace>"
  using assms
proof (induction rule:init_hoare.induct)
  case (SingleI \<Gamma> P ss Q sl)
  hence " \<Gamma> \<Turnstile> [P] ss [Q]"
    using seq_hoare3_soundness by auto
  then show ?case 
    unfolding init_hoare_valid_wt_def seq_hoare_valid2_wt_def using world_seq_exec.intros by fastforce
next
  case (ParallelI \<Gamma> P cs\<^sub>1 R cs\<^sub>2 Q)
  hence "\<Gamma> \<Turnstile>\<^sub>I \<lbrace>P\<rbrace> cs\<^sub>1 \<lbrace>R\<rbrace>" and "\<Gamma> \<Turnstile>\<^sub>I \<lbrace>R\<rbrace> cs\<^sub>2 \<lbrace>Q\<rbrace>"
    unfolding conc_stmt_wf_def by auto
  then show ?case 
    using parallelI_valid 
    by (metis ParallelI.prems(1) ParallelI.prems(2) ParallelI.prems(3))
next
  case (ParallelI2 \<Gamma> P cs\<^sub>2 R cs\<^sub>1 Q)
  hence "\<Gamma> \<Turnstile>\<^sub>I \<lbrace>P\<rbrace> cs\<^sub>2 \<lbrace>R\<rbrace>" and "\<Gamma> \<Turnstile>\<^sub>I \<lbrace>R\<rbrace> cs\<^sub>1 \<lbrace>Q\<rbrace>"
    unfolding conc_stmt_wf_def by auto
  have "\<Gamma> \<Turnstile>\<^sub>I \<lbrace>P\<rbrace> cs\<^sub>2 || cs\<^sub>1 \<lbrace>Q\<rbrace>"
    using parallelI_valid[OF `\<Gamma> \<Turnstile>\<^sub>I \<lbrace>P\<rbrace> cs\<^sub>2 \<lbrace>R\<rbrace>` `\<Gamma> \<Turnstile>\<^sub>I \<lbrace>R\<rbrace> cs\<^sub>1 \<lbrace>Q\<rbrace>`]
    `conc_stmt_wf (cs\<^sub>1 || cs\<^sub>2)` ` nonneg_delay_conc (cs\<^sub>1 || cs\<^sub>2)` `conc_wt \<Gamma> (cs\<^sub>1 || cs\<^sub>2)`
    unfolding conc_stmt_wf_def 
    by (metis conc_wt.intros(2) conc_wt_cases(2) disjoint_iff_not_equal distinct_append
    nonneg_delay_conc.simps(2) signals_from.simps(2))
  thus ?case
    using world_init_exec_commute
    unfolding init_hoare_valid_wt_def 
    by (smt ParallelI2.prems(1) parallelI_comp_commute' world_init_exec.intros world_init_exec_cases(2))
next
  case (ConseqI \<Gamma> P' P cs Q Q')
  then show ?case 
    by (smt init_hoare_valid_wt_def)
next
  case (ConjI \<Gamma> P cs Q1 Q2)
  then show ?case 
    by (simp add: init_hoare_valid_wt_def)
qed

definition wp3_init :: "'signal tyenv \<Rightarrow> 'signal conc_stmt \<Rightarrow> 'signal assn2 \<Rightarrow> 'signal assn2" where
  "wp3_init \<Gamma> cs Q = (\<lambda>tw. wityping \<Gamma> (snd tw) \<and> (\<forall>tw'. (tw, cs \<Rightarrow>\<^sub>I tw') \<longrightarrow> Q tw'))"

lemma wp3_init_single:
  "wp3_init \<Gamma> (process sl : ss) Q = wp3 \<Gamma> ss Q"
  apply (rule ext)
  unfolding wp3_init_def wp3_def
  by (smt init'_cases(1) world_init_exec_cases(1) world_init_exec_process world_seq_exec.intros)

lemma wp3_init_parallel:
  assumes "conc_stmt_wf (cs1 || cs2)" and "nonneg_delay_conc (cs1 || cs2)" and "conc_wt \<Gamma> (cs1 || cs2)"
  shows   "wp3_init \<Gamma> (cs1 || cs2) Q = wp3_init \<Gamma> cs1 (wp3_init \<Gamma> cs2 Q)"
  unfolding wp3_init_def
proof (rule, rule, rule_tac[!] conjI, simp, rule, rule, rule)
  fix tw tw'
  assume *: "wityping \<Gamma> (snd tw) \<and> (\<forall>tw'. tw , cs1 || cs2 \<Rightarrow>\<^sub>I tw' \<longrightarrow> Q tw')"
  assume "tw, cs1 \<Rightarrow>\<^sub>I tw'"
  thus   "wityping \<Gamma> (snd tw')"
    using init_preserve_wityping_semantic * unfolding init_hoare_valid_def 
    by (metis (no_types) \<open>tw , cs1 \<Rightarrow>\<^sub>I tw'\<close> assms(1) assms(2) assms(3) conc_stmt_wf_def
    conc_wt_cases(2) distinct_append init_hoare_valid_def init_preserve_wityping_semantic
    nonneg_delay_conc.simps(2) signals_from.simps(2))
  { fix tw2 
    assume "tw', cs2 \<Rightarrow>\<^sub>I tw2"
    hence "Q tw2"
      using * `tw, cs1 \<Rightarrow>\<^sub>I tw'` 
      by (metis assms(1) assms(2) conc_stmt_wf_def distinct_append nonneg_delay_conc.simps(2)
      signals_from.simps(2) world_init_equality world_init_exec_alt.intros(2)) }
  thus " \<forall>tw'a. tw' , cs2 \<Rightarrow>\<^sub>I tw'a \<longrightarrow> Q tw'a"
    by auto
next
  fix tw
  assume *: "wityping \<Gamma> (snd tw) \<and> (\<forall>tw'. tw , cs1 \<Rightarrow>\<^sub>I tw' \<longrightarrow> wityping \<Gamma> (snd tw') \<and> (\<forall>tw'a. tw' , cs2 \<Rightarrow>\<^sub>I tw'a \<longrightarrow> Q tw'a))"
  thus "wityping \<Gamma> (snd tw)"
    by auto
  { fix tw' 
    assume "tw, cs1 || cs2 \<Rightarrow>\<^sub>I tw'"
    hence "Q tw'"
      using *  by (meson assms(1) assms(2) exist_middle_worldline_init)  }
  thus "\<forall>tw'. tw , cs1 || cs2 \<Rightarrow>\<^sub>I tw' \<longrightarrow> Q tw'"
    by auto
qed

fun wp3_init_fun :: "'signal tyenv \<Rightarrow> 'signal conc_stmt \<Rightarrow> 'signal assn2 \<Rightarrow> 'signal assn2" where
  "wp3_init_fun \<Gamma> (process sl : ss) Q = wp3 \<Gamma> ss Q"
| "wp3_init_fun \<Gamma> (cs1 || cs2) Q = wp3_init_fun \<Gamma> cs1 (wp3_init_fun \<Gamma> cs2 Q)"

lemma wp3_init_fun_is_wp3_init:
  assumes "conc_stmt_wf cs" and "nonneg_delay_conc cs" and "conc_wt \<Gamma> cs"
  shows   "wp3_init_fun \<Gamma> cs Q = wp3_init \<Gamma> cs Q"
  using assms
  apply (induction cs arbitrary: Q)
  using wp3_init_parallel 
  apply (metis conc_stmt_wf_def conc_wt_cases(2) distinct_append nonneg_delay_conc.simps(2) signals_from.simps(2) wp3_init_fun.simps(2))
  by (simp add: wp3_init_single)

definition init_sim2_valid_wt :: "'signal tyenv \<Rightarrow> 'signal assn2 \<Rightarrow> 'signal conc_stmt \<Rightarrow> 'signal assn2 \<Rightarrow> bool" where
  "init_sim2_valid_wt \<Gamma> P cs Q = (\<forall>tw tw'. wityping \<Gamma> (snd tw) \<and> P tw \<and> init_sim2 tw cs tw' \<longrightarrow> Q tw')"

inductive
  init_sim2_hoare_wt :: "'signal tyenv \<Rightarrow> 'signal assn2 \<Rightarrow> 'signal conc_stmt \<Rightarrow> 'signal assn2 \<Rightarrow> bool" where
AssignI_suc: "\<Gamma> \<turnstile>\<^sub>I \<lbrace>P\<rbrace> cs \<lbrace>\<lambda>tw. Q (fst tw + 1, snd tw)\<rbrace>  \<Longrightarrow> init_sim2_hoare_wt \<Gamma> P cs Q" |
ConseqI_suc_sim: "\<forall>tw. P' tw \<longrightarrow> P tw \<Longrightarrow> init_sim2_hoare_wt \<Gamma> P cs Q \<Longrightarrow> \<forall>tw. Q tw \<longrightarrow> Q' tw \<Longrightarrow> init_sim2_hoare_wt \<Gamma> P' cs Q'" |
ConjI_suc_sim: "init_sim2_hoare_wt \<Gamma> P cs Q1 \<Longrightarrow> init_sim2_hoare_wt \<Gamma> P cs Q2 \<Longrightarrow> init_sim2_hoare_wt \<Gamma> P cs (\<lambda>tw. Q1 tw \<and> Q2 tw)"

lemma init_sim2_hoare_wt_soundness:
  assumes "init_sim2_hoare_wt \<Gamma> P cs Q"
  assumes "conc_stmt_wf cs" and "nonneg_delay_conc cs" and "conc_wt \<Gamma> cs"
  shows "init_sim2_valid_wt \<Gamma> P cs Q"
  using assms
proof (induction rule:init_sim2_hoare_wt.induct)
  case (AssignI_suc \<Gamma> P cs Q)
  have *: "\<Gamma> \<Turnstile>\<^sub>I \<lbrace>P\<rbrace> cs \<lbrace>\<lambda>tw. Q (fst tw + 1, snd tw)\<rbrace>"
    using soundness_init_hoare[OF AssignI_suc] by auto
  { fix tw tw'
    assume "P tw"
    assume "wityping \<Gamma> (snd tw)"
    assume "tw, cs \<Rightarrow>\<^sub>I tw'"
    hence "Q (fst tw' + 1, snd tw')" (is ?imp1)
      using * \<open>P tw\<close> `wityping \<Gamma> (snd tw)` unfolding init_hoare_valid_wt_def by blast
    have "init_sim2 tw cs (fst tw' + 1, snd tw')" (is ?imp2)
      using \<open>tw, cs \<Rightarrow>\<^sub>I tw'\<close>   using init_sim2.intros by blast
    hence "?imp1 \<and> ?imp2"
      using \<open>?imp1\<close> by auto }
  then show ?case
    unfolding init_sim2_valid_wt_def by auto
next
  case (ConseqI_suc_sim \<Gamma> P' P cs Q Q')
  then show ?case
    by (smt init_sim2_valid_wt_def)
next
  case (ConjI_suc_sim \<Gamma> P cs Q1 Q2)
  then show ?case   by (simp add: init_sim2_valid_wt_def)
qed

lemma init_sim2_preserves_wityping:
  assumes "init_sim2 tw cs tw'" and "conc_wt \<Gamma> cs" and "conc_stmt_wf cs" and "nonneg_delay_conc cs"
  assumes "wityping \<Gamma> (snd tw)"
  shows   "wityping \<Gamma> (snd tw')"
  using assms
proof (induction cs arbitrary: tw tw')
  case (Bpar cs1 cs2)
  then obtain tw2 where "tw, (cs1 || cs2) \<Rightarrow>\<^sub>I tw2" and "tw' = (fst tw2 + 1, snd tw2)"
    by (meson init_sim2.cases)
  then obtain tw_temp where "tw, cs1 \<Rightarrow>\<^sub>I tw_temp" and "tw_temp, cs2 \<Rightarrow>\<^sub>I tw2"
    by (meson Bpar.prems(3) Bpar.prems(4) exist_middle_worldline_init)
  hence "init_sim2 tw cs1 (fst tw_temp + 1, snd tw_temp)"
    using init_sim2.intros by blast
  note IH = Bpar(1)[OF this]
  hence " wityping \<Gamma> (snd tw_temp)"
    using Bpar unfolding conc_stmt_wf_def by auto
  have "init_sim2 tw_temp cs2 tw'"
    using `tw_temp, cs2 \<Rightarrow>\<^sub>I tw2` 
    using \<open>tw' = (get_time tw2 + 1, snd tw2)\<close> init_sim2.intros by blast
  note IH2 = Bpar(2)[OF this]
  thus "wityping \<Gamma> (snd tw')"
    using Bpar `wityping \<Gamma> (snd tw_temp)` unfolding conc_stmt_wf_def by auto    
next
  case (Bsingle sl ss)
  then obtain tw2 where *: "tw, process sl : ss \<Rightarrow>\<^sub>I tw2" and "tw' = (fst tw2 + 1, snd tw2)"
    by (meson init_sim2.cases)
  have "seq_wt \<Gamma> ss" using Bsingle by auto
  hence "wityping \<Gamma> (snd tw2)"
    using * VHDL_Hoare_Complete.soundness_init_hoare[OF single_conc_stmt_preserve_wityping_init_hoare[OF `seq_wt \<Gamma> ss`]]
    Bsingle(3-) unfolding init_hoare_valid_def  by meson
  thus ?case
    using `tw' = (fst tw2 + 1 , snd tw2)` by auto
qed

lemma grand_correctness:
  assumes "sim_fin2 w (i + 1) cs tw'" and "wityping \<Gamma> w"
  assumes "conc_stmt_wf cs" and "conc_wt \<Gamma> cs" and "nonneg_delay_conc cs"
  assumes "\<Gamma> \<turnstile>\<^sub>s \<lbrace>Inv\<rbrace> cs \<lbrace>Inv\<rbrace>"
  assumes "init_sim2_hoare_wt \<Gamma> (\<lambda>tw. fst tw = 0) cs Inv"
  shows   "Inv tw'"
proof -
  obtain tw where "init_sim2 (0, w) cs tw" and  "tw, i + 1, cs \<Rightarrow>\<^sub>S tw'"
    using sim_fin2.cases[OF `sim_fin2 w (i + 1) cs tw'`]  by metis
  hence "i + 1 = fst tw'"
    using world_maxtime_lt_fst_tres  by blast
  have "wityping \<Gamma> (snd tw)"
    using init_sim2_preserves_wityping 
    by (metis \<open>init_sim2 (0, w) cs tw\<close> assms(2-5) snd_conv)
  have "init_sim2_valid_wt \<Gamma> (\<lambda>tw. fst tw = 0) cs Inv"
    using init_sim2_hoare_wt_soundness[OF assms(7)] assms(2-5)  by auto
  hence "Inv tw"
    using \<open>init_sim2 (0, w) cs tw\<close> fst_conv assms(2) unfolding init_sim2_valid_wt_def
    by (metis snd_conv)    
  moreover have "\<Gamma> \<Turnstile>\<^sub>s \<lbrace>Inv\<rbrace> cs \<lbrace>Inv\<rbrace>"
    using conc_sim_soundness[OF assms(6)] assms(2-5) by auto
  ultimately have "Inv tw'"
    using \<open>tw, i + 1, cs \<Rightarrow>\<^sub>S tw'\<close> `wityping \<Gamma> (snd tw)` unfolding sim_hoare_valid_wt_def 
    by blast
  thus ?thesis
    by auto
qed

lemma grand_correctness2:
  assumes "sim_fin2 w endtime cs tw'" and "wityping \<Gamma> w"
  assumes "conc_stmt_wf cs" and "conc_wt \<Gamma> cs" and "nonneg_delay_conc cs"
  assumes "\<Gamma> \<turnstile>\<^sub>s \<lbrace>Inv\<rbrace> cs \<lbrace>Inv\<rbrace>"
  assumes "Q (0, w)"
  assumes "init_sim2_hoare_wt \<Gamma> (\<lambda>tw. fst tw = 0 \<and> Q tw) cs Inv"
  shows   "Inv tw'"
proof -
  obtain tw where "init_sim2 (0, w) cs tw" and  "tw, endtime, cs \<Rightarrow>\<^sub>S tw'"
    using sim_fin2.cases[OF `sim_fin2 w endtime cs tw'`]  by metis
  hence "endtime = fst tw'"
    using world_maxtime_lt_fst_tres  by blast  
  have "wityping \<Gamma> (snd tw)"
    using init_sim2_preserves_wityping 
    by (metis \<open>init_sim2 (0, w) cs tw\<close> assms(2-5) snd_conv)  
  have "init_sim2_valid_wt \<Gamma> (\<lambda>tw. fst tw = 0 \<and> Q tw) cs Inv"
    using init_sim2_hoare_wt_soundness[OF assms(8)] assms(2-5)  by auto
  hence "Inv tw"
    using \<open>init_sim2 (0, w) cs tw\<close> fst_conv assms(2) unfolding init_sim2_valid_wt_def
    by (metis assms(7) snd_conv)
  moreover have "\<Gamma> \<Turnstile>\<^sub>s \<lbrace>Inv\<rbrace> cs \<lbrace>Inv\<rbrace>"
    using conc_sim_soundness[OF assms(6)] assms(2-5) by auto
  ultimately have "Inv tw'"
    using \<open>tw, endtime, cs \<Rightarrow>\<^sub>S tw'\<close> `wityping \<Gamma> (snd tw)` unfolding sim_hoare_valid_wt_def 
    by blast
  thus ?thesis
    by auto
qed

end