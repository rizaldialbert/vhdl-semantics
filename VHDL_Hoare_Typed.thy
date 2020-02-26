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
| "eval_world_raw t w (Bsig_delayed sig dly) = snd w sig (t - dly)"
| "eval_world_raw t w (Bsig_event sig)    = Bv (sig \<in> event_of (t, w))"
| "eval_world_raw t w (Bnot e)            = (case eval_world_raw t w e of 
                                                    Bv bool   \<Rightarrow> Bv (\<not> bool)
                                                  | Lv ki bs  \<Rightarrow> Lv ki (map Not bs))"

| "eval_world_raw t w (Bslice sig l r)    = (case eval_world_raw t w (Bsig sig) of 
                                                   Lv ki bs \<Rightarrow>  Lv ki (nths bs {length bs - l - 1 .. length bs - r - 1}))"

| "eval_world_raw t w (Bindex sig idx)    = (case eval_world_raw t w (Bsig sig) of 
                                                   Lv ki bs \<Rightarrow>  Bv (bs ! idx))"


| "eval_world_raw t w (Bshiftl e n)       = (case eval_world_raw t w e of 
                                                    Lv ki bs  \<Rightarrow> Lv ki (drop n (bs @ replicate n False)))"

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
    apply (rule bexp_wt_cases(9)[OF 10(1)])
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
    by (metis eval_world_raw.simps(13) ty.distinct(1) type_of.elims)
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
    by (meson bexp_wt_cases(8) ty.distinct(1))
next
  case (17 t w sig idx)
  then show ?case 
    by (metis (no_types, lifting) bexp_wt_cases(10) bexp_wt_cases(9) eval_world_raw.simps(10)
    eval_world_raw.simps(17) is_Bv_def ty.simps(3) type_of.simps(1) val.case_eq_if wityping_def
    wtyping_def)
next
  case (18 t w e n)
  then show ?case 
    by (meson bexp_wt_cases(14) ty.distinct(1))
next
  case (19 t w e n)
  then show ?case 
    by (meson bexp_wt_cases(15) ty.distinct(1))
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
    apply (rule bexp_wt_cases(9)[OF 10(1)])
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
    by (metis (no_types, hide_lams) eval_world_raw.simps(13) ty.distinct(1) ty.inject type_of.elims)
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
    apply (rule bexp_wt_cases(8)[OF 16(2)])
    using 16 sorry
next
  case (17 t w sig idx)
  then show ?case bexp_wt_cases(8)
    (* by (metis (no_types, lifting) bexp_wt_cases(10) bexp_wt_cases(9) eval_world_raw.simps(10) eval_world_raw.simps(17) is_Bv_def ty.simps(3) type_of.simps(1) val.case_eq_if wityping_def wtyping_def) *)
next
  case (18 t w e n)
  then show ?case 
    (* by (meson bexp_wt_cases(14) ty.distinct(1)) *)
next
  case (19 t w e n)
  then show ?case 
    (* by (meson bexp_wt_cases(15) ty.distinct(1)) *)
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
    using bexp_wt_cases_lit 
    (* by blast *)
qed  



lemma
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
    then obtain res1 res2 where "eval_world_raw t w e1 = Lv ki res1" and "eval_world_raw t w e2 = Lv ki res2"
      using eval_world_raw_
    then show ?thesis sorry
  qed
next
  case (2 t w e1 e2)
  then show ?case sorry
next
  case (3 t w e1 e2)
  then show ?case sorry
next
  case (4 t w e1 e2)
  then show ?case sorry
next
  case (5 t w e1 e2)
  then show ?case sorry
next
  case (6 t w e1 e2)
  then show ?case sorry
next
  case (7 t w e1 e2)
  then show ?case sorry
next
  case (8 t w e1 e2)
  then show ?case sorry
next
  case (9 t w e1 e2)
  then show ?case sorry
next
  case (10 t w sig)
  then show ?case sorry
next
case (11 t w)
  then show ?case sorry
next
  case (12 t w)
then show ?case sorry
next
  case (13 t w sig dly)
  then show ?case sorry
next
  case (14 t w sig)
  then show ?case sorry
next
  case (15 t w e)
  then show ?case sorry
next
  case (16 t w sig l r)
  then show ?case sorry
next
  case (17 t w sig idx)
  then show ?case sorry
next
  case (18 t w e n)
  then show ?case sorry
next
  case (19 t w e n)
  then show ?case sorry
next
  case (20 t w th guard el)
  then show ?case sorry
next
  case (21 t w sign val)
  then show ?case sorry
qed
  




end