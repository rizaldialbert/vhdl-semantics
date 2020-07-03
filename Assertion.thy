(*
 * Copyright 2020, NTU
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 *  Author: Albert Rizaldi, NTU Singapore
 *)

theory Assertion
  imports VHDL_Hoare_Typed Bits_Int_Aux Cosine_Frac_Approx Fixed_Point
          "HOL-Library.Reflection"
begin  

datatype 'a sig = Sname 'a

datatype rsig = Svar nat (* | Snext rsig *)

primrec Irsig :: \<open>rsig \<Rightarrow> 'a sig list \<Rightarrow> 'a sig\<close> where
  Irsig_Var:  \<open>Irsig (Svar n) ss = ss ! n\<close>

lemmas Irsig_simps = Irsig_Var

fun highest_idx_rsig :: \<open>rsig \<Rightarrow> nat \<close> where
  \<open>highest_idx_rsig (Svar n) = n + 1\<close>

fun wf_rsig :: \<open>rsig \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool\<close> where
  \<open>wf_rsig (Svar n) len lo = (lo \<le> n \<and> n < len)\<close>

datatype rwline = Wvar nat | Adv rwline

primrec Irwline :: \<open>rwline \<Rightarrow> (nat \<times> 'a sig worldline_init) list \<Rightarrow> nat \<times> 'a sig worldline_init\<close> where
  "Irwline (Wvar n) ws = ws ! n"
| "Irwline (Adv t) ws  = (fst (Irwline t ws) + 1, snd (Irwline t ws))"

fun highest_rwline_idx :: \<open>rwline \<Rightarrow> nat\<close> where
  \<open>highest_rwline_idx (Wvar n) = n + 1\<close>
| \<open>highest_rwline_idx (Adv t) = highest_rwline_idx t\<close>

lemma 
  assumes "highest_rwline_idx x \<le> length ws"
  shows "Irwline (Adv x) ws = Irwline x  (map (\<lambda>tw. (Suc (get_time tw), snd tw)) ws)"
  using assms
  by (induction x) auto

fun increase_time_rwline :: "rwline \<Rightarrow> rwline" where
  "increase_time_rwline (Wvar n) = (Adv (Wvar n))"
| "increase_time_rwline (Adv t) = (Adv (Adv t))"
  
lemma 
  assumes "highest_rwline_idx x \<le> length ws"
  shows "Irwline (increase_time_rwline x) ws = Irwline x  (map (\<lambda>tw. (Suc (get_time tw), snd tw)) ws)"
  using assms 
proof (induction x)
  case (Wvar x)
  then show ?case by auto
next
  case (Adv x)
  hence **: "Irwline (increase_time_rwline x) ws = Irwline x (map (\<lambda>tw. (Suc (get_time tw), snd tw)) ws)"
    by auto
  have "Irwline (Adv x) (map (\<lambda>tw. (Suc (get_time tw), snd tw)) ws) = 
       (Suc (get_time (Irwline x (map (\<lambda>tw. (Suc (get_time tw), snd tw)) ws))), snd (Irwline x (map (\<lambda>tw. (Suc (get_time tw), snd tw)) ws)))"
    by auto
  also have "... = (Suc (fst (Irwline (increase_time_rwline x) ws)), snd (Irwline (increase_time_rwline x) ws))"
    unfolding ** by auto
  also have "... = (fst (Irwline (increase_time_rwline (Adv x)) ws), snd (Irwline (increase_time_rwline (Adv x)) ws))"
  proof -
    have "Suc (fst (Irwline (increase_time_rwline x) ws)) = fst (Irwline (increase_time_rwline (Adv x)) ws)"
      by (induction x) (auto)
    moreover have "snd (Irwline (increase_time_rwline x) ws) = snd (Irwline (increase_time_rwline (Adv x)) ws)"
      by (induction x) (auto)
    ultimately show ?thesis
      by auto
  qed
  also have "... =  Irwline (increase_time_rwline (Adv x)) ws "
    by auto
  finally show ?case
    by auto
qed
  
datatype rnat = NC nat| NVar nat| NSuc rnat | NDec rnat | NAdd rnat rnat | NSub rnat rnat | NFst rwline

fun Irnat :: "rnat  \<Rightarrow> nat list \<Rightarrow> (nat \<times> 'a sig worldline_init) list \<Rightarrow> nat"
where
  Irnat_Suc: "Irnat (NSuc t) ns ws = Suc (Irnat t ns ws)"
| Irnat_Fst: "Irnat (NFst w) ns ws = fst (Irwline w ws)"
| Irnat_Dec: "Irnat (NDec t) ns ws =     (Irnat t ns ws) - 1"
| Irnat_Var: "Irnat (NVar n) ns ws = ns ! n"
| Irnat_Add: "Irnat (NAdd s t) ns ws = Irnat s ns ws + Irnat t ns ws"
| Irnat_Sub: "Irnat (NSub s t) ns ws = Irnat s ns ws - Irnat t ns ws"
| Irnat_C:   "Irnat (NC i) ns ws = i"

lemma Irnat_C0: "Irnat (NC 0) ns ws = 0"
  by simp

lemma Irnat_C1: "Irnat (NC 1) ns ws = 1"
  by simp

lemma Irnat_Cnumeral: "Irnat (NC (numeral x)) ns ws = numeral x"
  by simp

lemmas Irnat_simps = Irnat_Suc  Irnat_Var Irnat_Add Irnat_Sub Irnat_Dec
  Irnat_C0 Irnat_C1 Irnat_Cnumeral Irnat_Fst

proposition "((x :: nat) + 1) - 1  + y + fst (tw :: nat \<times> 'a sig worldline_init) = 0"
  apply (reify Irnat_simps Irwline.simps ("((x::nat) + 1) - 1 + y + fst tw"))
  oops

fun highest_idx_rnat :: \<open>rnat \<Rightarrow> nat\<close> where 
  \<open>highest_idx_rnat (NSuc t) = highest_idx_rnat t\<close>
| \<open>highest_idx_rnat (NDec t) = highest_idx_rnat t\<close>
| \<open>highest_idx_rnat (NVar n) = n + 1\<close>
| \<open>highest_idx_rnat (NAdd s t) = max (highest_idx_rnat s) (highest_idx_rnat t)\<close>
| \<open>highest_idx_rnat (NSub s t) = max (highest_idx_rnat s) (highest_idx_rnat t)\<close>
| \<open>highest_idx_rnat (NFst w) = 0\<close>
| \<open>highest_idx_rnat (NC c) = 0\<close>

fun highest_idx_rnat_rwline :: \<open>rnat \<Rightarrow> nat\<close> where
  \<open>highest_idx_rnat_rwline (NFst w) = highest_rwline_idx w\<close>
| \<open>highest_idx_rnat_rwline (NSuc t) = highest_idx_rnat_rwline t\<close>
| \<open>highest_idx_rnat_rwline (NDec t) = highest_idx_rnat_rwline t\<close>
| \<open>highest_idx_rnat_rwline (NVar n) = 0\<close>
| \<open>highest_idx_rnat_rwline (NAdd s t) = max (highest_idx_rnat_rwline s) (highest_idx_rnat_rwline t)\<close>
| \<open>highest_idx_rnat_rwline (NSub s t) = max (highest_idx_rnat_rwline s) (highest_idx_rnat_rwline t)\<close>
| \<open>highest_idx_rnat_rwline (NC c) = 0\<close>

fun increase_time_rnat :: "rnat \<Rightarrow> rnat" where
  "increase_time_rnat (NFst w) = (NSuc (NFst w))"
| "increase_time_rnat (NSuc t) = (NSuc (increase_time_rnat t))"
| "increase_time_rnat (NDec t) = (NDec (increase_time_rnat t))"
| "increase_time_rnat (NVar n) = (NVar n)"
| "increase_time_rnat (NAdd t1 t2) = (NAdd (increase_time_rnat t1) (increase_time_rnat t2))"
| "increase_time_rnat (NSub t1 t2) = (NSub (increase_time_rnat t1) (increase_time_rnat t2))"
| "increase_time_rnat (NC c) = (NC c)"

lemma increase_time_rnat_correct:
  assumes \<open>highest_idx_rnat_rwline t \<le> length ws\<close>
  shows \<open>Irnat (increase_time_rnat t) ns ws = Irnat t ns (map (\<lambda>tw. (fst tw + 1, snd tw)) ws)\<close>
  using assms
proof (induction t)
  case (NFst x)
  hence "Irnat (increase_time_rnat (NFst x)) ns ws =  Suc (get_time (Irwline x ws))"
    by auto
  have " Irnat (NFst x) ns (map (\<lambda>tw. (get_time tw + 1, snd tw)) ws) = fst (Irwline x (map (\<lambda>tw. (Suc (get_time tw), snd tw)) ws))"
    by auto
  also have "... = Suc (get_time (Irwline x ws))"
    using NFst
  proof (induction x)
    case (Wvar x)
    then show ?case by auto
  next
    case (Adv x)
    then show ?case by auto
  qed
  then show ?case 
    by simp
qed auto


datatype rval = VC val | Vwline rwline rsig rnat

primrec Irval :: \<open>rval \<Rightarrow> 'a sig list \<Rightarrow> nat list \<Rightarrow> (nat \<times> 'a sig worldline_init) list \<Rightarrow> val\<close> where
             \<open>Irval (VC v) ss ns ws = v\<close>
| Irval_Wline: \<open>Irval (Vwline w s n) ss ns ws = wline_of (Irwline w ws) (Irsig s ss) (Irnat n ns ws)\<close>

fun highest_idx_rval_rsig :: \<open>rval \<Rightarrow> nat\<close> where
  \<open>highest_idx_rval_rsig (VC v) = 0\<close>
| \<open>highest_idx_rval_rsig (Vwline w s n) = highest_idx_rsig s\<close>

fun highest_idx_rval_rwline :: \<open>rval \<Rightarrow> nat\<close> where
  \<open>highest_idx_rval_rwline (VC v)  = 0\<close>
| \<open>highest_idx_rval_rwline (Vwline w s n)  = max (highest_rwline_idx w) (highest_idx_rnat_rwline n)\<close> 

fun highest_idx_rval_rnat :: \<open>rval \<Rightarrow> nat\<close> where
  \<open>highest_idx_rval_rnat (VC v)  = 0\<close>
| \<open>highest_idx_rval_rnat (Vwline w s n)  = highest_idx_rnat n\<close>

fun wf_rval_sig :: \<open>rval \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool\<close> where
  \<open>wf_rval_sig (VC v) len m = True\<close>
| \<open>wf_rval_sig (Vwline w s n) len m = wf_rsig s len m\<close>
                                                                                                           
lemma Irval_C:
  \<open>Irval (VC (Bv x)) ss ns ws = Bv x\<close>
  \<open>Irval (VC (Lv sign xs)) ss ns ws = Lv sign xs\<close>
  by auto

lemmas Irval_simps = Irval_Wline Irval_C

fun increase_time_rval :: "rval \<Rightarrow> rval" where
  \<open>increase_time_rval (VC v) = VC v\<close>
| \<open>increase_time_rval (Vwline w s n) = (Vwline w s (increase_time_rnat n))\<close>

lemma increase_time_rval_correct: 
  assumes \<open>highest_idx_rval_rwline t \<le> length ws\<close>
  shows \<open>Irval (increase_time_rval t) ss ns ws = Irval t ss ns (map (\<lambda>tw. (fst tw + 1, snd tw)) ws)\<close>
  using assms
proof (induction t)
  case (VC x)
  then show ?case by auto
next
  case (Vwline x1a x2a x3)
  have 0: "highest_idx_rnat_rwline x3 \<le> length ws"
    using Vwline(1) by auto
  have 1: "highest_rwline_idx x1a \<le> length ws"
    using Vwline(1) by auto
  have "Irval (increase_time_rval (Vwline x1a x2a x3)) ss ns ws = snd (snd (Irwline x1a ws)) (Irsig x2a ss) (Irnat (increase_time_rnat x3) ns ws)"
    by auto
  also have "... =  snd (snd (Irwline x1a ws)) (Irsig x2a ss) (Irnat x3 ns (map (\<lambda>tw. (get_time tw + 1, snd tw)) ws))"
    unfolding  increase_time_rnat_correct[OF 0] by auto
  also have "... = 
        snd (snd (Irwline x1a (map (\<lambda>tw. (Suc (get_time tw), snd tw)) ws))) (Irsig x2a ss) (Irnat x3 ns (map (\<lambda>tw. (Suc (get_time tw), snd tw)) ws))"
    using 1 by (induction x1a) auto
  also have "... = Irval (Vwline x1a x2a x3) ss ns (map (\<lambda>tw. (get_time tw + 1, snd tw)) ws)"
    by auto
  finally show ?case 
    by auto
qed
 
proposition
  \<open>wline_of tw (ACCUM :: 'a sig) i = Bv False\<close>
  apply (reify Irval_simps Irsig_simps Irnat_simps Irwline.simps ("wline_of tw ACCUM i"))
  apply (reify Irval_simps ("Bv False"))
  oops

datatype rset = LEmpty | LCons rsig rset 

primrec Irset :: "rset \<Rightarrow> 'a sig list \<Rightarrow> 'a sig set"
where
  "Irset (LEmpty) sis = {}"
| "Irset (LCons i t) sis = insert (Irsig i sis) (Irset t sis)"

proposition
  \<open>{ACCUM, COMMON, s :: 'a sig} \<noteq> {}\<close>
  apply (reify  Irset.simps Irsig_simps ("{ACCUM, COMMON, s}"))
  oops

fun highest_idx_rset :: \<open>rset \<Rightarrow> nat\<close> where
  \<open>highest_idx_rset LEmpty = 0\<close>
| \<open>highest_idx_rset (LCons sig col) = max (highest_idx_rsig sig) (highest_idx_rset col)\<close>

fun wf_rset_sig :: \<open>rset \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool\<close> where
  \<open>wf_rset_sig (LEmpty) len m = True\<close>
| \<open>wf_rset_sig (LCons i t) len m = (wf_rsig i len m \<and> wf_rset_sig t len m)\<close>

datatype rint = IC int |  IAdd rint rint | IMult rint rint
  | INeg rint | ISub rint rint | Ibin_of rval | Isbintrunc rnat rint
  | Islice rval rnat rnat | Iubin_of rval | Ibintrunc rnat rint

primrec Irint :: "rint \<Rightarrow> (nat \<times> 'a sig worldline_init) list \<Rightarrow> 'a sig list \<Rightarrow> nat list \<Rightarrow> int"
where
  Irint_Neg: "Irint (INeg t)  ws ss ns  = - Irint t  ws ss ns "
| Irint_Add: "Irint (IAdd s t)  ws ss ns  = Irint s  ws ss ns  + Irint t  ws ss ns "
| Irint_Sub: "Irint (ISub s t)  ws ss ns  = Irint s  ws ss ns  - Irint t  ws ss ns "
| Irint_Mult: "Irint (IMult s t)  ws ss ns  = Irint s  ws ss ns  * Irint t  ws ss ns "
| Irint_Bin: "Irint (Ibin_of v)  ws ss ns  = sbl_to_bin (lval_of (Irval v  ss ns ws))"
| Irint_Trunc: "Irint (Isbintrunc n i)  ws ss ns  = sbintrunc (Irnat n ns ws) (Irint i  ws ss ns )"
| Irint_Slice: "Irint (Islice v lo hi)  ws ss ns  = sbl_to_bin (nths (lval_of (Irval v  ss ns ws)) { Irnat lo ns ws .. Irnat hi ns ws})"
| Irint_Ubin: "Irint (Iubin_of v)  ws ss ns  = bl_to_bin (lval_of (Irval v  ss ns ws))"
| Irint_Trunc2: "Irint (Ibintrunc n i)  ws ss ns  = bintrunc (Irnat n ns ws) (Irint i  ws ss ns )"
| Irint_C: "Irint (IC i)  ws ss ns  = i"

lemma Irint_C0: "Irint (IC 0) ws ss ns = 0"
  by simp

lemma Irint_C1: "Irint (IC 1) ws ss ns = 1"
  by simp

lemma Irint_Cnumeral: "Irint (IC (numeral x)) ws ss ns = numeral x"
  by simp

lemmas Irint_simps = Irint_Neg Irint_Add Irint_Sub Irint_Mult Irint_C0 Irint_C1 Irint_Cnumeral
                     Irint_Bin Irint_Trunc Irint_Slice Irint_Ubin Irint_Trunc2

fun highest_idx_rint_rnat :: \<open>rint \<Rightarrow> nat \<close> where
  \<open>highest_idx_rint_rnat (IC n) = 0\<close>
| \<open>highest_idx_rint_rnat (IAdd s t) = max (highest_idx_rint_rnat s) (highest_idx_rint_rnat t)\<close>
| \<open>highest_idx_rint_rnat (IMult s t) = max (highest_idx_rint_rnat s) (highest_idx_rint_rnat t)\<close>
| \<open>highest_idx_rint_rnat (INeg s) = (highest_idx_rint_rnat s)\<close>
| \<open>highest_idx_rint_rnat (ISub s t) = max (highest_idx_rint_rnat s) (highest_idx_rint_rnat t)\<close>
| \<open>highest_idx_rint_rnat (Ibin_of v) = highest_idx_rval_rnat v\<close>
| \<open>highest_idx_rint_rnat (Isbintrunc s t) = max (highest_idx_rnat s) (highest_idx_rint_rnat t)\<close>
| \<open>highest_idx_rint_rnat (Islice v i j) = max (highest_idx_rval_rnat v) (max (highest_idx_rnat i) (highest_idx_rnat j))\<close>
| \<open>highest_idx_rint_rnat (Iubin_of v) = highest_idx_rval_rnat v\<close>
| \<open>highest_idx_rint_rnat (Ibintrunc s t) = max (highest_idx_rnat s) (highest_idx_rint_rnat t)\<close>

fun highest_idx_rint_rsig :: \<open>rint \<Rightarrow> nat\<close> where
  \<open>highest_idx_rint_rsig (Ibin_of v) = highest_idx_rval_rsig v\<close>
| \<open>highest_idx_rint_rsig (Islice v i j) = highest_idx_rval_rsig v\<close>
| \<open>highest_idx_rint_rsig (Iubin_of v) = highest_idx_rval_rsig v\<close>
| \<open>highest_idx_rint_rsig (IC n) = 0\<close>
| \<open>highest_idx_rint_rsig (IAdd s t) = max (highest_idx_rint_rsig s) (highest_idx_rint_rsig t)\<close>
| \<open>highest_idx_rint_rsig (IMult s t) = max (highest_idx_rint_rsig s) (highest_idx_rint_rsig t)\<close>
| \<open>highest_idx_rint_rsig (INeg s) = (highest_idx_rint_rsig s) \<close>
| \<open>highest_idx_rint_rsig (ISub s t) = max (highest_idx_rint_rsig s) (highest_idx_rint_rsig t)\<close>
| \<open>highest_idx_rint_rsig (Isbintrunc s t) = highest_idx_rint_rsig t\<close>
| \<open>highest_idx_rint_rsig (Ibintrunc s t) = highest_idx_rint_rsig t\<close>

fun highest_idx_rint_rwline :: \<open>rint \<Rightarrow> nat\<close> where
  \<open>highest_idx_rint_rwline (Ibin_of v) = highest_idx_rval_rwline v\<close>
| \<open>highest_idx_rint_rwline (Islice v i j) = max (highest_idx_rval_rwline v) (max (highest_idx_rnat_rwline i) (highest_idx_rnat_rwline j))\<close>
| \<open>highest_idx_rint_rwline (Iubin_of v) = highest_idx_rval_rwline v\<close>
| \<open>highest_idx_rint_rwline (IC n) = 0\<close>
| \<open>highest_idx_rint_rwline (IAdd s t) = max (highest_idx_rint_rwline s) (highest_idx_rint_rwline t)\<close>
| \<open>highest_idx_rint_rwline (IMult s t) = max (highest_idx_rint_rwline s) (highest_idx_rint_rwline t)\<close>
| \<open>highest_idx_rint_rwline (INeg s) = (highest_idx_rint_rwline s) \<close>
| \<open>highest_idx_rint_rwline (ISub s t) = max (highest_idx_rint_rwline s) (highest_idx_rint_rwline t)\<close>
| \<open>highest_idx_rint_rwline (Isbintrunc s t) = max (highest_idx_rnat_rwline s) (highest_idx_rint_rwline t)\<close>
| \<open>highest_idx_rint_rwline (Ibintrunc s t) = max (highest_idx_rnat_rwline s) (highest_idx_rint_rwline t)\<close>

fun wf_rint_sig :: \<open>rint \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool\<close> where
  \<open>wf_rint_sig (Ibin_of v) len m = wf_rval_sig v len m\<close>
| \<open>wf_rint_sig (Islice v i j) len m = wf_rval_sig v len m\<close>
| \<open>wf_rint_sig (Iubin_of v) len m = wf_rval_sig v len m\<close>
| \<open>wf_rint_sig (IC n) len m = True\<close>
| \<open>wf_rint_sig (IAdd s t) len m = (wf_rint_sig s len m \<and> wf_rint_sig t len m)\<close>
| \<open>wf_rint_sig (IMult s t) len m = (wf_rint_sig s len m \<and> wf_rint_sig t len m)\<close>
| \<open>wf_rint_sig (INeg s) len m = (wf_rint_sig s len m) \<close>
| \<open>wf_rint_sig (ISub s t) len m = (wf_rint_sig s len m \<and> wf_rint_sig t len m)\<close>
| \<open>wf_rint_sig (Isbintrunc s t) len m = wf_rint_sig t len m\<close>
| \<open>wf_rint_sig (Ibintrunc s t) len m = wf_rint_sig t len m\<close>

fun increase_time_rint :: \<open>rint \<Rightarrow> rint\<close> where
  \<open>increase_time_rint (Ibin_of v) = (Ibin_of (increase_time_rval v))\<close>
| \<open>increase_time_rint (Islice v i j) = (Islice (increase_time_rval v) (increase_time_rnat i) (increase_time_rnat j))\<close>
| \<open>increase_time_rint (Iubin_of v) = (Iubin_of (increase_time_rval v))\<close>
| \<open>increase_time_rint (IC n) = (IC n)\<close>
| \<open>increase_time_rint (IAdd s t) = IAdd (increase_time_rint s) (increase_time_rint t)\<close>
| \<open>increase_time_rint (IMult s t) = IMult (increase_time_rint s) (increase_time_rint t)\<close>
| \<open>increase_time_rint (INeg s) = INeg (increase_time_rint s)\<close>
| \<open>increase_time_rint (ISub s t) = ISub (increase_time_rint s) (increase_time_rint t)\<close>
| \<open>increase_time_rint (Isbintrunc s t) = Isbintrunc (increase_time_rnat s) (increase_time_rint t)\<close>
| \<open>increase_time_rint (Ibintrunc s t) = Ibintrunc (increase_time_rnat s) (increase_time_rint t)\<close>

lemma increase_time_rint_correct:
  assumes \<open>highest_idx_rint_rwline t \<le> length ws\<close>
  shows \<open>Irint (increase_time_rint t) ws ss ns = Irint t (map (\<lambda>tw. (fst tw + 1, snd tw)) ws) ss ns\<close>
  using assms
  by (induction t) (auto simp add: increase_time_rval_correct increase_time_rnat_correct)

datatype form 
  = RF 
  | RT
  | RElof rsig rset
  | RNLT rnat rnat 
  | RILT rint rint 
  | RBval rval
  | RDisevt rset rwline
  | RAnd form form 
  | ROr form form
  | RImp form form
  | RBImp form form
  | Rnot form
  | RSigex rset form 
  | RNex form 
  | RSigall rset form
  | RNall form
  | RVEq rval rval
  | RIfte form form form
  | RIEq rint rint
  | Rsepand form form 

fun highest_idx_form_nat :: \<open>form \<Rightarrow> nat\<close> where
  \<open>highest_idx_form_nat (RSigex col f) = highest_idx_form_nat f\<close> 
| \<open>highest_idx_form_nat (RSigall col f) = highest_idx_form_nat f\<close>
| \<open>highest_idx_form_nat (RAnd f1 f2) = max (highest_idx_form_nat f1) (highest_idx_form_nat f2)\<close>
| \<open>highest_idx_form_nat (ROr f1 f2) = max (highest_idx_form_nat f1)  (highest_idx_form_nat f2)\<close>
| \<open>highest_idx_form_nat (RImp f1 f2) = max (highest_idx_form_nat f1) (highest_idx_form_nat f2)\<close>
| \<open>highest_idx_form_nat (RBImp f1 f2) = max (highest_idx_form_nat f1) (highest_idx_form_nat f2)\<close>
| \<open>highest_idx_form_nat (Rnot f) = highest_idx_form_nat f\<close>
| \<open>highest_idx_form_nat (RNex f) = highest_idx_form_nat f - 1\<close> 
| \<open>highest_idx_form_nat (RNall f) = highest_idx_form_nat f - 1\<close>
| \<open>highest_idx_form_nat (RIfte g t e) = max (highest_idx_form_nat g) (max (highest_idx_form_nat t)  (highest_idx_form_nat e))\<close>
| \<open>highest_idx_form_nat RT = 0\<close>
| \<open>highest_idx_form_nat RF = 0\<close>
| \<open>highest_idx_form_nat (RElof sig col) = 0\<close>
| \<open>highest_idx_form_nat (RNLT v va) = max (highest_idx_rnat v) (highest_idx_rnat va)\<close>
| \<open>highest_idx_form_nat (RILT v va) = max (highest_idx_rint_rnat v) (highest_idx_rint_rnat va)\<close>
| \<open>highest_idx_form_nat (RBval v) = highest_idx_rval_rnat v\<close>
| \<open>highest_idx_form_nat (RDisevt v va) = 0\<close>
| \<open>highest_idx_form_nat (RVEq v va) = max (highest_idx_rval_rnat v) (highest_idx_rval_rnat va)\<close>
| \<open>highest_idx_form_nat (RIEq i1 i2) = max (highest_idx_rint_rnat i1) (highest_idx_rint_rnat i2)\<close>
| \<open>highest_idx_form_nat (Rsepand t1 t2) =  (highest_idx_form_nat t1) + (highest_idx_form_nat t2)\<close>

fun highest_idx_form_sig :: \<open>form \<Rightarrow> nat\<close> where
  \<open>highest_idx_form_sig (RSigex col f) = max (highest_idx_rset col - 1) (highest_idx_form_sig f - 1)\<close> 
| \<open>highest_idx_form_sig (RSigall col f) = max (highest_idx_rset col - 1) (highest_idx_form_sig f - 1)\<close>
| \<open>highest_idx_form_sig (RAnd f1 f2) = max (highest_idx_form_sig f1) (highest_idx_form_sig f2)\<close>
| \<open>highest_idx_form_sig (ROr f1 f2) = max (highest_idx_form_sig f1)  (highest_idx_form_sig f2)\<close>
| \<open>highest_idx_form_sig (RImp f1 f2) = max (highest_idx_form_sig f1) (highest_idx_form_sig f2)\<close>
| \<open>highest_idx_form_sig (RBImp f1 f2) = max (highest_idx_form_sig f1) (highest_idx_form_sig f2)\<close>
| \<open>highest_idx_form_sig (Rnot f) = highest_idx_form_sig f\<close>
| \<open>highest_idx_form_sig (RNex f) = highest_idx_form_sig f\<close> 
| \<open>highest_idx_form_sig (RNall f) = highest_idx_form_sig f\<close>
| \<open>highest_idx_form_sig (RIfte g t e) = max (highest_idx_form_sig g) (max (highest_idx_form_sig t)  (highest_idx_form_sig e))\<close>
| \<open>highest_idx_form_sig RT = 0\<close>
| \<open>highest_idx_form_sig RF = 0\<close>
| \<open>highest_idx_form_sig (RElof v va) = max (highest_idx_rsig v) (highest_idx_rset va)\<close>
| \<open>highest_idx_form_sig (RNLT v va) = 0\<close>
| \<open>highest_idx_form_sig (RILT v va) = max (highest_idx_rint_rsig v) (highest_idx_rint_rsig va)\<close>
| \<open>highest_idx_form_sig (RBval v) = highest_idx_rval_rsig v\<close>
| \<open>highest_idx_form_sig (RDisevt v va) = highest_idx_rset v\<close>
| \<open>highest_idx_form_sig (RVEq v va) = max (highest_idx_rval_rsig v) (highest_idx_rval_rsig va)\<close>
| \<open>highest_idx_form_sig (RIEq i1 i2) = max (highest_idx_rint_rsig i1) (highest_idx_rint_rsig i2)\<close>
| \<open>highest_idx_form_sig (Rsepand i1 i2) = (highest_idx_form_sig i1) + (highest_idx_form_sig i2)\<close>

fun highest_idx_form_rwline :: \<open>form \<Rightarrow> nat\<close> where
  \<open>highest_idx_form_rwline (RSigex col f) = highest_idx_form_rwline f\<close> 
| \<open>highest_idx_form_rwline (RSigall col f) = highest_idx_form_rwline f\<close>
| \<open>highest_idx_form_rwline (RAnd f1 f2) = max (highest_idx_form_rwline f1) (highest_idx_form_rwline f2)\<close>
| \<open>highest_idx_form_rwline (ROr f1 f2) = max (highest_idx_form_rwline f1)  (highest_idx_form_rwline f2)\<close>
| \<open>highest_idx_form_rwline (RImp f1 f2) = max (highest_idx_form_rwline f1) (highest_idx_form_rwline f2)\<close>
| \<open>highest_idx_form_rwline (RBImp f1 f2) = max (highest_idx_form_rwline f1) (highest_idx_form_rwline f2)\<close>
| \<open>highest_idx_form_rwline (Rnot f) = highest_idx_form_rwline f\<close>
| \<open>highest_idx_form_rwline (RNex f) = highest_idx_form_rwline f\<close> 
| \<open>highest_idx_form_rwline (RNall f) = highest_idx_form_rwline f\<close>
| \<open>highest_idx_form_rwline (RIfte g t e) = max (highest_idx_form_rwline g) (max (highest_idx_form_rwline t)  (highest_idx_form_rwline e))\<close>
| \<open>highest_idx_form_rwline RT = 0\<close>
| \<open>highest_idx_form_rwline RF = 0\<close>
| \<open>highest_idx_form_rwline (RElof v va) = 0\<close>
| \<open>highest_idx_form_rwline (RNLT v va) = max (highest_idx_rnat_rwline v) (highest_idx_rnat_rwline va)\<close>
| \<open>highest_idx_form_rwline (RBval v) = highest_idx_rval_rwline v\<close>
| \<open>highest_idx_form_rwline (RDisevt v va) = highest_rwline_idx va\<close>
| \<open>highest_idx_form_rwline (RVEq v va) = max (highest_idx_rval_rwline v) (highest_idx_rval_rwline va)\<close>
| \<open>highest_idx_form_rwline (RIEq i1 i2) = max (highest_idx_rint_rwline i1) (highest_idx_rint_rwline i2)\<close>
| \<open>highest_idx_form_rwline (RILT i1 i2) = max (highest_idx_rint_rwline i1) (highest_idx_rint_rwline i2)\<close>
| \<open>highest_idx_form_rwline (Rsepand i1 i2) = max (highest_idx_form_rwline i1) (highest_idx_form_rwline i2)\<close>

function eval :: \<open>form \<Rightarrow> (nat \<times> 'a sig worldline_init) list \<Rightarrow> nat list \<Rightarrow> 'a sig list \<Rightarrow> bool\<close> where
  \<open>eval RT ws ns sis  = True\<close>
| \<open>eval RF ws ns sis  = False\<close>
| \<open>eval (RElof sig col) ws ns sis  =((Irsig sig sis) \<in> (Irset col sis))\<close>
| \<open>eval (RNLT n1 n2) ws ns sis  =(Irnat n1 ns ws < Irnat n2 ns ws)\<close>
| \<open>eval (RBval v) ws ns sis  =(bval_of (Irval v sis ns ws))\<close>
| \<open>eval (RDisevt s w) ws ns sis  =(disjnt (Irset s sis) (event_of (Irwline w ws)))\<close>
| \<open>eval (RAnd f1 f2) ws ns sis  =(eval f1 ws ns sis  \<and> eval f2 ws ns sis  )\<close>
| \<open>eval (ROr f1 f2) ws ns sis  =(eval f1 ws ns sis  \<or> eval f2 ws ns sis )\<close>
| \<open>eval (RImp f1 f2) ws ns sis  =(eval f1 ws ns sis  \<longrightarrow> eval f2 ws ns sis )\<close>
| \<open>eval (RBImp f1 f2) ws ns sis  =(eval f1 ws ns sis  \<longleftrightarrow> eval f2 ws ns sis )\<close>
| \<open>eval (RSigex col f) ws ns sis  =(\<exists>s :: 'a sig. eval (RAnd (RElof (Svar 0) col) f) ws ns (s # sis) )\<close>
| \<open>eval (RNex f) ws ns sis  =(\<exists>n :: nat. eval f ws (n # ns) sis )\<close>
| \<open>eval (RSigall col f) ws ns sis  =(\<forall>s :: 'a sig. eval (RImp (RElof (Svar 0) col) f) ws ns (s # sis) )\<close>
| \<open>eval (RNall f) ws ns sis  =(\<forall>n :: nat. eval f ws (n # ns) sis )\<close>
| \<open>eval (Rnot f) ws ns sis  =(\<not> (eval f ws ns sis ))\<close>
| \<open>eval (RVEq t1 t2) ws ns sis  = (Irval t1 sis ns ws = Irval t2 sis ns ws)\<close>
| \<open>eval (RIfte g t e) ws ns sis  = (if eval g ws ns sis  then eval t ws ns sis  else eval e ws ns sis )\<close>
| \<open>eval (RIEq t1 t2) ws ns sis  = (Irint t1 ws sis ns = Irint t2 ws sis ns)\<close>
| \<open>eval (RILT t1 t2) ws ns sis  = (Irint t1 ws sis ns < Irint t2 ws sis ns)\<close>
| \<open>eval (Rsepand t1 t2) ws ns sis = ( eval t1 ws (take (highest_idx_form_nat t1) ns) (take (highest_idx_form_sig t1) sis)
                                    \<and> eval t2 ws (drop (highest_idx_form_nat t1) ns) (drop (highest_idx_form_sig t1) sis))\<close>
  by pat_completeness auto
termination by size_change

fun wf_form_sig :: \<open>form \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool\<close> where
  \<open>wf_form_sig RT len   n =  True\<close>
| \<open>wf_form_sig RF len   n =  True\<close>
| \<open>wf_form_sig (RElof sig col) len n =  (wf_rsig sig len n \<and> wf_rset_sig col len n)\<close>
| \<open>wf_form_sig (RNLT n1 n2) len n =   True\<close>                     
| \<open>wf_form_sig (RBval v) len   n =  (wf_rval_sig v len n)\<close>
| \<open>wf_form_sig (RDisevt s w) len   n =  (wf_rset_sig s len n )\<close>
| \<open>wf_form_sig (RAnd f1 f2) len   n =  (wf_form_sig f1 len n  \<and> wf_form_sig f2 len n )\<close>
| \<open>wf_form_sig (ROr f1 f2) len   n = (wf_form_sig f1 len n \<and> wf_form_sig f2 len n )\<close>
| \<open>wf_form_sig (RImp f1 f2) len   n = (wf_form_sig f1 len n \<and> wf_form_sig f2 len n )\<close>
| \<open>wf_form_sig (RBImp f1 f2) len   n = (wf_form_sig f1 len n \<and> wf_form_sig f2 len n )\<close>
| \<open>wf_form_sig (RSigex col f) len   n =  (wf_rset_sig col (len + 1) (n + 1)  \<and> wf_form_sig f (len + 1) n)\<close>
| \<open>wf_form_sig (RNex f) len   n =   (wf_form_sig f len n)\<close>
| \<open>wf_form_sig (RSigall col f) len   n =  (wf_rset_sig col (len + 1) (n + 1)  \<and> wf_form_sig f (len + 1) n)\<close>
| \<open>wf_form_sig (RNall f) len   n =  (wf_form_sig f len n )\<close>
| \<open>wf_form_sig (Rnot f) len   n = (wf_form_sig f len n )\<close>
| \<open>wf_form_sig (RVEq t1 t2) len   n =  (wf_rval_sig t1 len n \<and> wf_rval_sig t2 len n)\<close>
| \<open>wf_form_sig (RIfte g t e) len   n =  (wf_form_sig g len n \<and> wf_form_sig t len n \<and> wf_form_sig e len n )\<close>
| \<open>wf_form_sig (RIEq t1 t2) len   n =  (wf_rint_sig t1 len n \<and> wf_rint_sig t2 len n)\<close>
| \<open>wf_form_sig (RILT t1 t2) len   n =  (wf_rint_sig t1 len n \<and> wf_rint_sig t2 len n)\<close>
| \<open>wf_form_sig (Rsepand t1 t2) len  n =  (highest_idx_form_sig t1 \<le> len \<and> wf_form_sig t1 (highest_idx_form_sig t1) n \<and> wf_form_sig t2 (len - (highest_idx_form_sig t1)) n)\<close>

lemmas eval_simps = eval.simps(1-17)

fun increase_time :: \<open>form \<Rightarrow> form\<close> where
    \<open>increase_time RF = RF\<close>
  | \<open>increase_time RT = RT\<close>
  | \<open>increase_time (RElof s col) = RElof s col\<close>
  | \<open>increase_time (RNLT t1 t2) = RNLT (increase_time_rnat t1) (increase_time_rnat t2)\<close>
  | \<open>increase_time (RBval t) = RBval (increase_time_rval t)\<close>
  | \<open>increase_time (RDisevt s w) = RDisevt s (Adv w)\<close>
  | \<open>increase_time (RAnd f1 f2) = RAnd (increase_time f1) (increase_time f2)\<close>
  | \<open>increase_time (ROr f1 f2) = ROr (increase_time f1) (increase_time f2)\<close>
  | \<open>increase_time (RImp f1 f2) = RImp (increase_time f1) (increase_time f2)\<close>
  | \<open>increase_time (RBImp f1 f2) = RBImp (increase_time f1) (increase_time f2)\<close>
  | \<open>increase_time (RSigex col f) = RSigex (col) (increase_time f)\<close>
  | \<open>increase_time (RNex f) = RNex (increase_time f)\<close>
  | \<open>increase_time (RSigall col f) = RSigall col (increase_time f)\<close>
  | \<open>increase_time (RNall f) = RNall (increase_time f)\<close>
  | \<open>increase_time (Rnot f) = Rnot (increase_time f)\<close>
  | \<open>increase_time (RVEq t1 t2) = RVEq (increase_time_rval t1) (increase_time_rval t2)\<close>
  | \<open>increase_time (RIfte g t e) = RIfte (increase_time g) (increase_time t) (increase_time e)\<close>
  | \<open>increase_time (RIEq t1 t2) = RIEq (increase_time_rint t1) (increase_time_rint t2)\<close>
  | \<open>increase_time (RILT t1 t2) = RILT (increase_time_rint t1) (increase_time_rint t2)\<close>
  | \<open>increase_time (Rsepand t1 t2) = Rsepand (increase_time t1) (increase_time t2)\<close>

thm increase_time_rint_correct

lemma highest_idx_rnat_increase_time [simp]:
  shows \<open>highest_idx_rnat (increase_time_rnat x1) = highest_idx_rnat x1\<close>
  by (induction x1) (auto)

lemma highest_idx_rval_rnat_increase_time [simp]:
  shows \<open>highest_idx_rval_rnat (increase_time_rval x) = highest_idx_rval_rnat x\<close>
  by (induction x) (auto simp add: highest_idx_rnat_increase_time)

lemma highest_idx_rint_rnat_increase_time [simp]:
  shows \<open>highest_idx_rint_rnat (increase_time_rint x1) = highest_idx_rint_rnat x1\<close>
  by (induction x1)
     (auto simp add: highest_idx_rval_rnat_increase_time highest_idx_rnat_increase_time)
  
lemma highest_idx_form_nat_increase_time [simp]:
  shows \<open>highest_idx_form_nat (increase_time f1) = highest_idx_form_nat f1\<close>
  by (induction f1)
     (auto simp add: highest_idx_rnat_increase_time highest_idx_rval_rnat_increase_time highest_idx_rint_rnat_increase_time)

lemma highest_idx_rval_rsig_increase_time [simp]:
  shows \<open>highest_idx_rval_rsig (increase_time_rval x1) = highest_idx_rval_rsig x1\<close>
  by (induction x1) (auto)

lemma highest_idx_rint_rsig_increase_time [simp]:
  shows \<open>highest_idx_rint_rsig (increase_time_rint x1) = highest_idx_rint_rsig x1\<close>
  by (induction x1)
     (auto simp add: highest_idx_rval_rsig_increase_time) 

lemma highest_idx_form_sig_increase_time [simp]:
  shows \<open>highest_idx_form_sig (increase_time f1) = highest_idx_form_sig f1\<close>
  by (induction f1)
     (auto simp add: highest_idx_rval_rsig_increase_time highest_idx_rint_rsig_increase_time)

lemma Irwline_adv_alt_def:
  assumes "highest_rwline_idx x2 \<le> length ws"
  shows "Irwline (Adv x2) ws = Irwline x2 (map (\<lambda>tw. (Suc (get_time tw), snd tw)) ws)"
  using assms
proof (induction x2)
  case (Wvar x)
  then show ?case by auto
next
  case (Adv x2)
  hence "Irwline (Adv x2) ws = Irwline x2 (map (\<lambda>tw. (Suc (get_time tw), snd tw)) ws)"
    by auto
  have "Irwline (Adv (Adv x2)) ws = (Suc (Suc (get_time (Irwline x2 ws))), snd (Irwline x2 ws))"
    by auto
  moreover have "Suc (Suc (fst (Irwline x2 ws))) = Suc (get_time (Irwline x2 (map (\<lambda>tw. (Suc (get_time tw), snd tw)) ws)))"
    by (metis Irwline.simps(2) Pair_inject Suc_eq_plus1 \<open>Irwline (Adv x2) ws = Irwline x2 (map (\<lambda>tw. (Suc (get_time tw), snd tw)) ws)\<close> prod.collapse)
  moreover have "snd (Irwline x2 ws) = snd (Irwline x2 (map (\<lambda>tw. (Suc (get_time tw), snd tw)) ws))"
    using Adv 
    by (metis Irwline.simps(2) \<open>Irwline (Adv x2) ws = Irwline x2 (map (\<lambda>tw. (Suc (get_time tw), snd tw)) ws)\<close> eq_snd_iff)  
  ultimately show ?case 
    by auto
qed

lemma eval_increase_time_correct:
  assumes \<open>highest_idx_form_rwline f \<le> length ws\<close>
  shows \<open>eval (increase_time f) ws ns ss = eval f (map (\<lambda>tw. (fst tw + 1, snd tw)) ws) ns ss\<close>
  using assms
proof (induction f arbitrary: ns ss)
  case (RDisevt x1 x2)
  have "eval (increase_time (RDisevt x1 x2)) ws ns ss = disjnt (Irset x1 ss) (event_of (Irwline (Adv x2) ws))"
    by auto
  also have "... = disjnt (Irset x1 ss) (event_of (Irwline x2 (map (\<lambda>tw. (Suc (get_time tw), snd tw)) ws)))"
    using Irwline_adv_alt_def RDisevt.prems by force
  finally show ?case 
    by auto
next
  case (RSigex x1 f)
  have "eval (increase_time (RSigex x1 f)) ws ns ss =  (\<exists>s. s \<in> Irset x1 (s # ss) \<and> eval (increase_time f) ws ns (s # ss))"
    by auto
  also have "... = (\<exists>s. s \<in> Irset x1 (s # ss) \<and> eval f (map (\<lambda>tw. (Suc (get_time tw), snd tw)) ws) ns (s # ss))"
  proof
    assume "\<exists>s. s \<in> Irset x1 (s # ss) \<and> eval (increase_time f) ws ns (s # ss)"
    then obtain s where "s \<in> Irset x1 (s # ss)" and "eval (increase_time f) ws ns (s # ss)"
      by auto
    hence "eval f (map (\<lambda>tw. (get_time tw + 1, snd tw)) ws) ns (s # ss)"
      using RSigex by auto
    thus "\<exists>s. s \<in> Irset x1 (s # ss) \<and> eval f (map (\<lambda>tw. (Suc (get_time tw), snd tw)) ws) ns (s # ss)"
      by (intro exI[where x="s"])(auto simp add: `s \<in> Irset x1 (s # ss)`)
  next
    assume "\<exists>s. s \<in> Irset x1 (s # ss) \<and> eval f (map (\<lambda>tw. (Suc (get_time tw), snd tw)) ws) ns (s # ss)"
    then obtain s where "s \<in> Irset x1 (s # ss)" and "eval f (map (\<lambda>tw. (Suc (get_time tw), snd tw)) ws) ns (s # ss)"
      by auto
    hence "eval (increase_time f) ws ns (s # ss)"
      using RSigex by auto
    thus "\<exists>s. s \<in> Irset x1 (s # ss) \<and> eval (increase_time f) ws ns (s # ss) "
      by (intro exI[where x="s"])(auto simp add: `s \<in> Irset x1 (s # ss)`)
  qed
  finally show ?case 
    by auto
next
  case (RNex f)
  have "eval (increase_time (RNex f)) ws ns ss = (\<exists>n. eval (increase_time f) ws (n # ns) ss)"
    by auto
  also have " ... = (\<exists>n. eval f (map (\<lambda>tw. (Suc (get_time tw), snd tw)) ws) (n # ns) ss)"
  proof 
    have " highest_idx_form_rwline f \<le> length ws"
      using RNex by auto
    assume "(\<exists>n. eval (increase_time f) ws (n # ns) ss)"
    then obtain n where "eval (increase_time f) ws (n # ns) ss"
      by auto
    hence "eval f (map (\<lambda>tw. (Suc (fst tw), snd tw)) ws) (n # ns) ss"
      using RNex(1)[OF `highest_idx_form_rwline f \<le> length ws`] by auto
    thus "(\<exists>n. eval f (map (\<lambda>tw. (Suc (get_time tw), snd tw)) ws) (n # ns) ss)"
      by (intro exI[where x="n"])
  next
    have " highest_idx_form_rwline f \<le> length ws"
      using RNex by auto
    assume "(\<exists>n. eval f (map (\<lambda>tw. (Suc (get_time tw), snd tw)) ws) (n # ns) ss)"
    then obtain n where "eval f (map (\<lambda>tw. (Suc (fst tw), snd tw)) ws) (n # ns) ss"
      by auto
    hence "eval (increase_time f) ws (n # ns) ss"
      using RNex(1)[OF `highest_idx_form_rwline f \<le> length ws`] by auto
    thus "(\<exists>n. eval (increase_time f) ws (n # ns) ss)"
      by (intro exI)
  qed
  finally show ?case 
    by auto
next
  case (RSigall x1 f)
  hence **: "highest_idx_form_rwline f \<le> length ws"
    by auto
  have " eval (increase_time (RSigall x1 f)) ws ns ss = (\<forall>s. s \<in> Irset x1 (s # ss) \<longrightarrow> eval (increase_time f) ws ns (s # ss))"
    by auto
  also have "... = (\<forall>s. s \<in> Irset x1 (s # ss) \<longrightarrow> eval f (map (\<lambda>tw. (Suc (get_time tw), snd tw)) ws) ns (s # ss))"
  proof 
    assume *: "\<forall>s. s \<in> Irset x1 (s # ss) \<longrightarrow> eval (increase_time f) ws ns (s # ss)"
    show " \<forall>s. s \<in> Irset x1 (s # ss) \<longrightarrow> eval f (map (\<lambda>tw. (Suc (get_time tw), snd tw)) ws) ns (s # ss)"
    proof (rule, rule)
      fix s 
      assume "s \<in> Irset x1 (s # ss)"
      hence "eval (increase_time f) ws ns (s # ss)"
        using * by auto
      thus "eval f (map (\<lambda>tw. (Suc (fst tw), snd tw)) ws) ns (s # ss)"
        using RSigall(1)[OF **] by auto
    qed
  next
    assume *: " \<forall>s. s \<in> Irset x1 (s # ss) \<longrightarrow> eval f (map (\<lambda>tw. (Suc (get_time tw), snd tw)) ws) ns (s # ss)"
    show "\<forall>s. s \<in> Irset x1 (s # ss) \<longrightarrow> eval (increase_time f) ws ns (s # ss)"
    proof (rule, rule)
      fix s
      assume "s \<in> Irset x1 (s # ss)"
      with * have "eval f (map (\<lambda>tw. (Suc (fst tw), snd tw)) ws) ns (s # ss)"
        by auto
      thus "eval (increase_time f) ws ns (s # ss)"
        using RSigall(1)[OF **] by auto
    qed
  qed
  finally show ?case 
    by auto
next
  case (RNall f)
  hence "highest_idx_form_rwline f \<le> length ws"
    by auto
  have "eval (increase_time (RNall f)) ws ns ss = (\<forall>n. eval (increase_time f) ws (n # ns) ss)"
    by auto
  also have "... =   (\<forall>n. eval f (map (\<lambda>tw. (Suc (get_time tw), snd tw)) ws) (n # ns) ss)"
    apply (rule iff_allI)
    using RNall(1)[OF `highest_idx_form_rwline f \<le> length ws`] by auto
  then show ?case 
    by auto
next
  case (Rsepand f1 f2)
  hence "highest_idx_form_rwline f1 \<le> length ws" and " highest_idx_form_rwline f2 \<le> length ws"
    by auto
  have "eval (increase_time (Rsepand f1 f2)) ws ns ss = 
    (eval (increase_time f1) ws (take (highest_idx_form_nat (increase_time f1)) ns) (take (highest_idx_form_sig (increase_time f1)) ss) \<and>
     eval (increase_time f2) ws (drop (highest_idx_form_nat (increase_time f1)) ns) (drop (highest_idx_form_sig (increase_time f1)) ss))"
    by auto
  also have "... = 
    (eval f1 (map (\<lambda>tw. (get_time tw + 1, snd tw)) ws) (take (highest_idx_form_nat (increase_time f1)) ns) (take (highest_idx_form_sig (increase_time f1)) ss) \<and>
     eval f2 (map (\<lambda>tw. (get_time tw + 1, snd tw)) ws) (drop (highest_idx_form_nat (increase_time f1)) ns) (drop (highest_idx_form_sig (increase_time f1)) ss))"
    using Rsepand by auto
  also have "... =
    (eval f1 (map (\<lambda>tw. (Suc (get_time tw), snd tw)) ws) (take (highest_idx_form_nat f1) ns) (take (highest_idx_form_sig f1) ss) \<and>
     eval f2 (map (\<lambda>tw. (Suc (get_time tw), snd tw)) ws) (drop (highest_idx_form_nat f1) ns) (drop (highest_idx_form_sig f1) ss))"
    by (auto simp add: highest_idx_form_nat_increase_time highest_idx_form_sig_increase_time)
  finally show ?case 
    by auto
qed (auto simp add: increase_time_rval_correct increase_time_rnat_correct increase_time_rint_correct)

                                          
experiment begin

abbreviation "V_INIT \<equiv> Lv Neu [False, False, False]" 
abbreviation "V_WAIT \<equiv> Lv Neu [False, False, True ]"
abbreviation "V_PRE  \<equiv> Lv Neu [False, True , False]"
abbreviation "V_PROC \<equiv> Lv Neu [False, True , True ]"
abbreviation "V_POST \<equiv> Lv Neu [True , False, False]" 

abbreviation "U_ZERO3  \<equiv>  [False, False, False]"
abbreviation "U_ZERO32 \<equiv>  replicate 32 False"

abbreviation "V_ZERO3   \<equiv> Lv Uns U_ZERO3"
abbreviation "V_ZERO32  \<equiv> Lv signedness.Sig U_ZERO32"


proposition
  \<open>disjnt {CLK :: 'a sig} (event_of tw) \<or> wline_of tw (CLK) (fst tw) \<noteq> (Bv True)\<close>
  apply (reify eval.simps Irwline.simps Irnat_simps Irsig_simps Irval_simps Irset.simps)
  oops

proposition
  fixes tw :: "nat \<times> 'a sig worldline_init"
  shows \<open>disjnt {CLK} (event_of tw) \<or> wline_of tw (CLK) (fst tw) \<noteq> (Bv True) \<longrightarrow> 
          (\<forall>n :: nat. fst tw < n \<longrightarrow> (\<forall>s. s \<in> {ACCUM, COUNTER, FRAC, COMMON, STATE, OUTREADY_REG} \<longrightarrow> wline_of tw s n = wline_of tw s (fst tw)))\<close>
  apply (reify eval.simps Irwline.simps Irnat_simps Irsig_simps Irval_simps Irset.simps)
  oops

proposition
  fixes tw :: "nat \<times> 'a sig worldline_init"
  shows \<open>\<forall>s::'a sig. s \<in> {ACCUM, COUNTER, FRAC, COMMON, STATE, OUTREADY_REG} \<longrightarrow> 1 < fst tw\<close>
  apply (reify eval_simps Irwline.simps Irnat_simps Irsig_simps Irval_simps Irset.simps)
  oops

schematic_goal
  \<open>eval ?x ?y ?z (?a :: 'a sig list) = (\<forall>s :: 'a sig. s \<in> {} \<longrightarrow> (\<exists>s2. s2 \<in> {ACCUM:: 'a sig, COUNTER} \<and> (\<forall>s3 :: 'a sig. s3 \<in> {} \<longrightarrow> True)))\<close> 
  apply (reify eval_simps Irsig_simps Irset.simps ("(\<forall>s :: 'a sig. s \<in> {} \<longrightarrow> (\<exists>s2. s2 \<in> {ACCUM :: 'a sig, COUNTER} \<and> (\<forall>s3 :: 'a sig. s3 \<in> {} \<longrightarrow> True)))"))
  by rule
  
proposition
  fixes tw :: "nat \<times> 'a sig worldline_init"
  fixes CLK RST :: "'a sig"
  shows \<open>if wline_of tw CLK ((fst tw - 1) - 1) = Bv False \<and> wline_of tw CLK (fst tw - 1) = Bv True
         then if bval_of (wline_of tw RST (fst tw - 1)) 
              then wline_of tw (s :: 'a sig) (fst tw) = wline_of tw (s :: 'a sig) (fst tw)
              else wline_of tw (s :: 'a sig) (fst tw) = wline_of tw (next_signal s) (fst tw - 1)
         else wline_of tw (s :: 'a sig) (fst tw) = wline_of tw (s :: 'a sig) (fst tw - 1)\<close> 
  apply (reify eval_simps Irwline.simps Irnat_simps Irsig_simps Irval_simps Irset.simps)
  oops

proposition
  fixes tw :: "nat \<times> 'a sig worldline_init"
  shows \<open>\<forall>s. s \<in> {ACCUM, COUNTER, FRAC, COMMON, STATE, OUTREADY_REG} \<longrightarrow> 1 < fst tw \<longrightarrow> 
             (if (wline_of tw CLK ((fst tw - 1) - 1) = Bv False)
              then if bval_of (wline_of tw RST (fst tw - 1)) 
                   then wline_of tw s (fst tw) = wline_of tw (s :: 'a sig) (fst tw)
                   else wline_of tw s (fst tw) = wline_of tw s (fst tw - 1)
              else wline_of tw s (fst tw) = wline_of tw s (fst tw - 1))\<close>
  apply (reify eval_simps Irwline.simps Irnat_simps Irsig_simps Irval_simps Irset.simps)
  (* seems like hitting some walls for reification here *)
  oops

proposition 
  fixes tw :: "nat \<times> 'a sig worldline_init"
  shows \<open>if wline_of tw STATE (fst tw - 1) = V_INIT
         then wline_of tw NEXT_STATE (fst tw) = V_WAIT
         else if wline_of tw STATE (fst tw - 1) = V_WAIT 
              then if bval_of (wline_of tw INREADY (fst tw - 1))
                   then wline_of tw NEXT_STATE (fst tw) = V_PRE 
                   else wline_of tw NEXT_STATE (fst tw) = V_WAIT
              else if wline_of tw STATE (fst tw - 1) = V_PRE
                   then wline_of tw NEXT_STATE (fst tw) = V_PROC
                   else if wline_of tw STATE (fst tw - 1) = V_PROC
                        then if bval_of (wline_of tw CTR_NEQ_0 (fst tw - 1))
                             then wline_of tw NEXT_STATE (fst tw) = V_PROC 
                             else wline_of tw NEXT_STATE (fst tw) = V_POST
                        else if wline_of tw STATE (fst tw - 1) = V_POST
                             then wline_of tw NEXT_STATE (fst tw) = V_WAIT
                             else wline_of tw NEXT_STATE (fst tw) = V_INIT
        \<close>
  apply (reify eval.simps Irwline.simps Irnat_simps Irsig_simps Irval_simps Irset.simps)
  oops  

proposition
  fixes tw :: "nat \<times> 'a sig worldline_init"
  shows \<open>disjnt {STATE, INREADY, CTR_NEQ_0} (event_of tw) \<longrightarrow> 
         (\<forall>i. fst tw < i \<longrightarrow> wline_of tw NEXT_STATE i = wline_of tw NEXT_STATE (fst tw))\<close>
  apply (reify eval.simps Irwline.simps Irnat_simps Irsig_simps Irval_simps Irset.simps)
  oops  

proposition
  fixes tw :: \<open>nat \<times> 'a sig worldline_init\<close>
  shows \<open> if wline_of tw STATE (fst tw - 1) = V_INIT 
          then sbl_to_bin (lval_of (wline_of tw (s :: 'a sig) (fst tw))) = 0
          else if wline_of tw STATE (fst tw - 1) = V_WAIT
               then if bval_of (wline_of tw INREADY (fst tw - 1)) 
                    then sbl_to_bin (lval_of (wline_of tw s (fst tw))) = sbl_to_bin (lval_of (wline_of tw INPUT  (fst tw - 1)))
                    else sbl_to_bin (lval_of (wline_of tw s (fst tw))) = sbl_to_bin (lval_of (wline_of tw COMMON (fst tw - 1)))
               else if wline_of tw STATE (fst tw - 1) = V_PRE
                    then sbl_to_bin (lval_of (wline_of tw s (fst tw))) = sbintrunc 31 (- sbl_to_bin (nths (lval_of (wline_of tw SQUARE_TEMP (fst tw - 1))) {1 .. 32}))
                    else if wline_of tw STATE (fst tw - 1) = V_PROC
                         then sbl_to_bin (lval_of (wline_of tw (s :: 'a sig) (fst tw))) = sbintrunc 31 (- sbl_to_bin (lval_of (wline_of tw COMMON (fst tw - 1))))
                         else sbl_to_bin (lval_of (wline_of tw (s :: 'a sig) (fst tw))) = sbl_to_bin (lval_of (wline_of tw (s :: 'a sig) (fst tw - 1)))\<close>
  apply (reify eval.simps Irwline.simps Irnat_simps Irsig_simps Irval_simps Irset.simps Irint_simps)
  oops

proposition 
  fixes tw :: \<open>nat \<times> 'a sig worldline_init\<close>
  shows "disjnt {STATE, COMMON, INREADY, INPUT, SQUARE_TEMP} (event_of tw) \<longrightarrow> 
                          (\<forall>i. fst tw < i \<longrightarrow> wline_of tw NEXT_COMMON i = wline_of tw NEXT_COMMON (fst tw))"
  apply (reify eval.simps Irwline.simps Irnat_simps Irsig_simps Irval_simps Irset.simps Irint_simps)
  oops

proposition 
  fixes tw :: \<open>nat \<times> 'a sig worldline_init\<close>
  shows \<open>sbl_to_bin (lval_of (wline_of tw SQUARE_TEMP (fst tw))) = 
         sbintrunc 63 (sbl_to_bin (lval_of (wline_of tw COMMON (fst tw - 1))) * 
                       sbl_to_bin (lval_of (wline_of tw COMMON (fst tw - 1))))\<close> 
  apply (reify eval.simps Irwline.simps Irnat_simps Irsig_simps Irval_simps Irset.simps Irint_simps)
  oops

proposition 
  fixes tw :: \<open>nat \<times> 'a sig worldline_init\<close>
  shows \<open>disjnt {COMMON} (event_of tw) \<longrightarrow> 
        (\<forall>i > fst tw. sbl_to_bin (lval_of (wline_of tw SQUARE_TEMP i)) = 
                      sbl_to_bin (lval_of (wline_of tw SQUARE_TEMP (fst tw))))\<close>
  apply (reify eval.simps Irwline.simps Irnat_simps Irsig_simps Irval_simps Irset.simps Irint_simps)
  oops

proposition
  fixes tw :: \<open>nat \<times> 'a sig worldline_init\<close>
  shows \<open>if wline_of tw STATE (fst tw - 1) = V_WAIT 
         then if bval_of (wline_of tw INREADY (fst tw - 1))
              then bl_to_bin (lval_of (wline_of tw NEXT_COUNTER (fst tw))) = 4
              else bl_to_bin (lval_of (wline_of tw NEXT_COUNTER (fst tw))) = 
                   bl_to_bin (lval_of (wline_of tw COUNTER (fst tw - 1)))
         else if wline_of tw STATE (fst tw - 1) = V_PRE
              then bl_to_bin (lval_of (wline_of tw NEXT_COUNTER (fst tw))) = bintrunc 3 (bl_to_bin (lval_of (wline_of tw COUNTER (fst tw - 1))) - 1)
              else if wline_of tw STATE (fst tw - 1) = V_PROC
                   then if bval_of (wline_of tw CTR_NEQ_0 (fst tw - 1))
                        then bl_to_bin (lval_of (wline_of tw NEXT_COUNTER (fst tw))) = bintrunc 3 (bl_to_bin (lval_of (wline_of tw COUNTER (fst tw - 1))) - 1)
                        else bl_to_bin (lval_of (wline_of tw NEXT_COUNTER (fst tw))) = bl_to_bin (lval_of (wline_of tw COUNTER (fst tw - 1)))
                   else if bval_of (wline_of tw CTR_NEQ_0 (fst tw - 1))
                        then bl_to_bin (lval_of (wline_of tw NEXT_COUNTER (fst tw))) = 0 
                        else bl_to_bin (lval_of (wline_of tw NEXT_COUNTER (fst tw))) = bl_to_bin (lval_of (wline_of tw COUNTER (fst tw - 1)))
        \<close>
  apply (reify eval.simps Irwline.simps Irnat_simps Irsig_simps Irval_simps Irset.simps Irint_simps)
  oops

proposition
  fixes tw :: \<open>nat \<times> 'a sig worldline_init\<close>
  shows \<open>disjnt {STATE, INREADY, CTR_NEQ_0, COUNTER} (event_of tw) \<longrightarrow> 
            (\<forall>i. fst tw < i \<longrightarrow> wline_of tw NEXT_COUNTER i = wline_of tw NEXT_COUNTER (fst tw))  \<close>
  apply (reify eval.simps Irwline.simps Irnat_simps Irsig_simps Irval_simps Irset.simps Irint_simps)
  oops

end

datatype assertion = Abs (get_form : form)

primrec interp_assertion :: "assertion \<Rightarrow> nat list \<Rightarrow> 'a sig list \<Rightarrow> 'a sig assn2" where
  "interp_assertion (Abs f) ns sis = (\<lambda>tw. eval f [tw] ns sis)"

primrec interp_assertion_suc :: \<open>assertion \<Rightarrow> nat list \<Rightarrow> 'a sig list \<Rightarrow> 'a sig assn2\<close> where
  "interp_assertion_suc (Abs f) ns sis = (\<lambda>tw. eval f [(fst tw + 1, snd tw)] ns sis)"

fun wf_assertion :: \<open>assertion \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool\<close> where
  "wf_assertion (Abs f) n s = (highest_idx_form_rwline f \<le> 1 \<and> highest_idx_form_nat f = n \<and> highest_idx_form_sig f = s)"

experiment begin

proposition 
  fixes tw :: \<open>nat \<times> 'a sig worldline_init\<close>
  shows "1 < fst tw"
    apply (reify eval.simps Irwline.simps Irnat_simps Irsig_simps Irval_simps Irset.simps Irint_simps
               interp_assertion.simps ("1 < fst tw"))
  oops

declare [[show_types]]

lemma
  \<open>eval ( (RImp (RDisevt (LCons (Svar (Suc (Suc (Suc (Suc 0))))) (LCons (Svar (Suc (Suc (Suc 0)))) (LCons (Svar (Suc (Suc 0))) (LCons (Svar (Suc 0)) LEmpty)))) (Wvar 0))
        (RNall (RImp (RNLT (NFst (Wvar 0)) (NVar 0)) (RVEq (Vwline (Wvar 0) (Svar 0) (NVar 0)) (Vwline (Wvar 0) (Svar 0) (NFst (Wvar 0)))))))) [tw] [] [NEXT_COUNTER, COUNTER, CTR_NEQ_0, INREADY, STATE] 
  = ((disjnt {STATE, INREADY, CTR_NEQ_0, COUNTER} (event_of tw) \<longrightarrow> 
            (\<forall>i. fst tw < i \<longrightarrow> wline_of tw NEXT_COUNTER i = wline_of tw NEXT_COUNTER (fst tw))))\<close>
  by auto

proposition
  "interp_assertion (Abs ((RImp (RDisevt (LCons (Svar (Suc (Suc (Suc (Suc 0))))) (LCons (Svar (Suc (Suc (Suc 0)))) (LCons (Svar (Suc (Suc 0))) (LCons (Svar (Suc 0)) LEmpty)))) (Wvar 0))
        (RNall (RImp (RNLT (NFst (Wvar 0)) (NVar 0)) (RVEq (Vwline (Wvar 0) (Svar 0) (NVar 0)) (Vwline (Wvar 0) (Svar 0) (NFst (Wvar 0)))))))))  [] [NEXT_COUNTER, COUNTER, CTR_NEQ_0, INREADY, STATE] = 
    (\<lambda>tw. disjnt {STATE, INREADY, CTR_NEQ_0, COUNTER} (event_of tw) \<longrightarrow> 
            (\<forall>i. fst tw < i \<longrightarrow> wline_of tw NEXT_COUNTER i = wline_of tw NEXT_COUNTER (fst tw)))"
  by simp

schematic_goal 
  "highest_idx_form_rwline ((RImp (RDisevt (LCons (Svar (Suc (Suc (Suc (Suc 0))))) (LCons (Svar (Suc (Suc (Suc 0)))) (LCons (Svar (Suc (Suc 0))) (LCons (Svar (Suc 0)) LEmpty)))) (Wvar 0))
        (RNall (RImp (RNLT (NFst (Wvar 0)) (NVar 0)) (RVEq (Vwline (Wvar 0) (Svar 0) (NVar 0)) (Vwline (Wvar 0) (Svar 0) (NFst (Wvar 0)))))))) = ?x"
  by simp
  
end

datatype hoare_triple = Hoare (pre_hoare: assertion) (post_hoare : assertion)

primrec interp_hoare_conc :: \<open>hoare_triple  \<Rightarrow> nat list \<Rightarrow> 'a sig list \<Rightarrow> 
                                               nat list \<Rightarrow> 'a sig list \<Rightarrow> 'a sig tyenv \<Rightarrow> 'a sig conc_stmt \<Rightarrow> bool\<close> where
  \<open>interp_hoare_conc (Hoare pre post) ns1 ss1 ns2 ss2 \<Gamma> cs = (\<Gamma> \<Turnstile> \<lbrace>interp_assertion pre ns1 ss1\<rbrace> cs \<lbrace>interp_assertion post ns2 ss2\<rbrace>)\<close>

primrec interp_hoare_conc_suc :: \<open>hoare_triple \<Rightarrow> nat list \<Rightarrow> 'a sig list \<Rightarrow> 
                                               nat list \<Rightarrow> 'a sig list \<Rightarrow> 'a sig tyenv \<Rightarrow> 'a sig conc_stmt \<Rightarrow> bool\<close> where
  \<open>interp_hoare_conc_suc (Hoare pre post) ns1 ss1 ns2 ss2 \<Gamma> cs = (\<Gamma> \<Turnstile> \<lbrace>interp_assertion pre ns1 ss1\<rbrace> cs \<lbrace>interp_assertion_suc post ns2 ss2\<rbrace>)\<close>

primrec interp_hoare_seq :: \<open>hoare_triple \<Rightarrow>  nat list \<Rightarrow> 'a sig list \<Rightarrow> 
                                              nat list \<Rightarrow> 'a sig list \<Rightarrow> 'a sig tyenv \<Rightarrow> 'a sig seq_stmt \<Rightarrow> bool\<close> where
  \<open>interp_hoare_seq (Hoare pre post) ns1 ss1 ns2 ss2 \<Gamma> ss = (\<Gamma> \<Turnstile> [interp_assertion pre ns1 ss1] ss [interp_assertion post ns2 ss2])\<close>

primrec interp_hoare_seq_suc :: \<open>hoare_triple \<Rightarrow>  nat list \<Rightarrow> 'a sig list \<Rightarrow> 
                                              nat list \<Rightarrow> 'a sig list \<Rightarrow> 'a sig tyenv \<Rightarrow> 'a sig seq_stmt \<Rightarrow> bool\<close> where
  \<open>interp_hoare_seq_suc (Hoare pre post) ns1 ss1 ns2 ss2 \<Gamma> ss = (\<Gamma> \<Turnstile> [interp_assertion pre ns1 ss1] ss [interp_assertion_suc post ns2 ss2])\<close>

lemma
  \<open>\<Gamma> \<Turnstile> \<lbrace>P\<rbrace> cs \<lbrace>Q1\<rbrace> \<Longrightarrow> \<Gamma> \<Turnstile> \<lbrace>P\<rbrace> cs \<lbrace>Q2\<rbrace> \<Longrightarrow> \<Gamma> \<Turnstile> \<lbrace>P\<rbrace> cs \<lbrace>\<lambda>tw. Q1 tw \<and> Q2 tw\<rbrace>\<close>
  by (simp add: conc_hoare_valid_wt_def)

lemma Irnat_worldline_upd2:
  \<open>Irnat t ns ((tw[ sig, dly :=\<^sub>2 v] # ws)) = Irnat t ns (tw # ws)\<close>
proof (induction t)
  case (NFst x)
  then show ?case 
  proof (induction x)
    case (Wvar xa)
    then show ?case 
      by (induction xa) auto
  qed auto
qed auto

lemma Irnat_worldline_inert_upd2:
  \<open>Irnat t ns ((tw\<lbrakk> sig, dly :=\<^sub>2 v\<rbrakk> # ws)) = Irnat t ns (tw # ws)\<close>
proof (induction t)
  case (NFst x)
  then show ?case 
  proof (induction x)
    case (Wvar xa)
    then show ?case 
      by (induction xa) (auto simp add: worldline_inert_upd2_def)
  qed auto
qed auto

lemma Irval_free_vars:
  assumes \<open>sig \<notin> set ss\<close> and \<open>wf_rval_sig x (length ss) m\<close>
  shows   \<open> Irval x ss ns (tw[ sig, dly :=\<^sub>2 v] # ws) =  Irval x ss ns (tw # ws)\<close>
  using assms
proof (induction x)
  case (VC x)
  then show ?case by auto
next
  case (Vwline x1a x2a x3)
  then show ?case 
  proof (induction x1a)
    case (Wvar xa)
    then show ?case 
    proof (induction xa)
      case 0
      have "Irsig x2a ss \<noteq> sig \<or> Irsig x2a ss = sig"
        by auto
      moreover
      { assume "Irsig x2a ss \<noteq> sig"
        hence ?case
          by (auto simp add: Irnat_worldline_upd2 ) (simp add: worldline_upd2_def worldline_upd_def) }
      moreover
      { assume "Irsig x2a ss = sig"
        then obtain n where "x2a = Svar n \<and> ss ! n = sig"
          by (metis Irsig_Var highest_idx_rsig.cases)
        hence \<open>n < length ss\<close>
          using 0 by auto 
        hence "sig \<in> set ss"
          using \<open>x2a = Svar n \<and> ss ! n = sig\<close> nth_mem by blast
        with \<open>sig \<notin> set ss\<close> have False by auto
        hence ?case
          by auto }
      ultimately show ?case by (auto simp add: Irnat_worldline_upd2 )
    next
      case (Suc xa)
      hence \<open>Irval (Vwline (Wvar xa) x2a x3) ss ns (tw[ sig, dly :=\<^sub>2 v] # ws) = Irval (Vwline (Wvar xa) x2a x3) ss ns (tw # ws)\<close>
        by auto
      then show ?case 
        by (auto simp add: Irnat_worldline_upd2)
    qed
  qed auto
qed

lemma Irval_free_vars2:
  assumes \<open>sig \<notin> set ss\<close> and \<open>wf_rval_sig x (length ss) m\<close>
  shows   \<open> Irval x ss ns (tw[ sig, dly :=\<^sub>2 v][sig', dly' :=\<^sub>2 v'] # ws) =  Irval x ss ns (tw[sig', dly' :=\<^sub>2 v'] # ws)\<close>
  using assms
proof (induction x)
  case (VC x)
  then show ?case by auto
next
  case (Vwline x1a x2a x3)
  then show ?case 
  proof (induction x1a)
    case (Wvar xa)
    then show ?case 
    proof (induction xa)
      case 0
      have "Irsig x2a ss \<noteq> sig \<or> Irsig x2a ss = sig"
        by auto
      moreover
      { assume "Irsig x2a ss \<noteq> sig"
        hence ?case
          by (auto simp add: Irnat_worldline_upd2 ) (simp add: worldline_upd2_def worldline_upd_def) }
      moreover
      { assume "Irsig x2a ss = sig"
        then obtain n where "x2a = Svar n \<and> ss ! n = sig"
          by (metis Irsig_Var highest_idx_rsig.cases)
        hence \<open>n < length ss\<close>
          using 0 by auto 
        hence "sig \<in> set ss"
          using \<open>x2a = Svar n \<and> ss ! n = sig\<close> nth_mem by blast
        with \<open>sig \<notin> set ss\<close> have False by auto
        hence ?case
          by auto }
      ultimately show ?case by (auto simp add: Irnat_worldline_upd2 )
    next
      case (Suc xa)
      hence \<open>Irval (Vwline (Wvar xa) x2a x3) ss ns (tw[ sig, dly :=\<^sub>2 v][ sig', dly' :=\<^sub>2 v'] # ws) = Irval (Vwline (Wvar xa) x2a x3) ss ns (tw[ sig', dly' :=\<^sub>2 v'] # ws)\<close>
        by auto
      then show ?case 
        by (auto simp add: Irnat_worldline_upd2)
    qed
  qed auto
qed

lemma Irval_free_vars_inert:
  assumes \<open>sig \<notin> set ss\<close> and \<open>wf_rval_sig x (length ss) m\<close>
  shows   \<open> Irval x ss ns (tw\<lbrakk> sig, dly :=\<^sub>2 v\<rbrakk> # ws) =  Irval x ss ns (tw # ws)\<close>
  using assms
proof (induction x)
  case (VC x)
  then show ?case by auto
next
  case (Vwline x1a x2a x3)
  then show ?case 
  proof (induction x1a)
    case (Wvar xa)
    then show ?case 
    proof (induction xa)
      case 0
      have "Irsig x2a ss \<noteq> sig \<or> Irsig x2a ss = sig"
        by auto
      moreover
      { assume "Irsig x2a ss \<noteq> sig"
        hence ?case
          by (auto simp add: Irnat_worldline_inert_upd2 ) (simp add: worldline_inert_upd2_def worldline_inert_upd_def) }
      moreover
      { assume "Irsig x2a ss = sig"
        then obtain n where "x2a = Svar n \<and> ss ! n = sig"
          by (metis Irsig_Var highest_idx_rsig.cases)
        hence \<open>n < length ss\<close>
          using 0 by auto 
        hence "sig \<in> set ss"
          using \<open>x2a = Svar n \<and> ss ! n = sig\<close> nth_mem by blast
        with \<open>sig \<notin> set ss\<close> have False by auto
        hence ?case
          by auto }
      ultimately show ?case by (auto simp add: Irnat_worldline_upd2 )
    next
      case (Suc xa)
      hence \<open>Irval (Vwline (Wvar xa) x2a x3) ss ns (tw\<lbrakk> sig, dly :=\<^sub>2 v\<rbrakk> # ws) = Irval (Vwline (Wvar xa) x2a x3) ss ns (tw # ws)\<close>
        by auto
      then show ?case 
        by (auto simp add: Irnat_worldline_inert_upd2)
    qed
  qed auto
qed

lemma disjnt_free_vars:
  assumes \<open>sig \<notin> set ss\<close> and \<open>wf_rset_sig x1 (length ss) m\<close> and \<open>highest_rwline_idx x2 \<le> length ws + 1\<close>
  shows \<open>disjnt (Irset x1 ss) (event_of (Irwline x2 (tw[ sig, dly :=\<^sub>2 v] # ws))) = 
         disjnt (Irset x1 ss) (event_of (Irwline x2 (tw # ws)))\<close>
proof -
  have "sig \<notin> Irset x1 ss"
    using assms
  proof (induction x1)
    case LEmpty
    then show ?case by auto
  next
    case (LCons x11 x12)
    then show ?case 
      by (induction x11) auto
  qed
  have "\<And>n. event_of (Irwline x2 ((n, snd tw [ sig, dly :=\<^sub>2 v]) # ws)) = event_of (Irwline x2 ((n, snd tw) # ws)) \<union> {sig} \<or> 
            event_of (Irwline x2 ((n, snd tw [ sig, dly :=\<^sub>2 v]) # ws)) = event_of (Irwline x2 ((n, snd tw) # ws)) - {sig}"
    using assms(3)
  proof (induction x2 arbitrary: ws )
    case (Wvar xa)
    then show ?case 
    proof (induction xa)
      case 0
      then show ?case 
          by (auto simp add: event_of_alt_def worldline_upd2_def worldline_upd_def)
    next
      case (Suc xa)
      then show ?case by auto
    qed
  next
    case (Adv x2)
    hence " Irwline (Adv x2) ((n, snd tw[ sig, dly :=\<^sub>2 v]) # ws) = Irwline x2 (map (\<lambda>tw. (Suc (get_time tw), snd tw)) ((n, snd tw[ sig, dly :=\<^sub>2 v]) # ws))"
      using Irwline_adv_alt_def by fastforce
    also have "... = Irwline x2 ((n + 1, snd tw[sig, dly :=\<^sub>2 v]) # map (\<lambda>tw. (Suc (get_time tw), snd tw)) ws)"
      by auto
    finally have 0: "Irwline (Adv x2) ((n, snd tw[ sig, dly :=\<^sub>2 v]) # ws) = Irwline x2 ((n + 1, snd tw[sig, dly :=\<^sub>2 v]) # map (\<lambda>tw. (Suc (get_time tw), snd tw)) ws)"
      by auto
    have "Irwline (Adv x2) ((n, snd tw) # ws) = Irwline x2 (map (\<lambda>tw. (Suc (fst tw),  snd tw)) ((n, snd tw) # ws))"
      using Adv Irwline_adv_alt_def by fastforce
    hence *: "Irwline (Adv x2) ((n, snd tw) # ws) = Irwline x2 ((n + 1, snd tw) # map (\<lambda>tw. (Suc (fst tw),  snd tw)) ws)"
      by auto
    hence "event_of (Irwline (Adv x2) ((n, snd tw[ sig, dly :=\<^sub>2 v]) # ws) ) = 
           event_of (Irwline x2 ((n + 1, snd tw[sig, dly :=\<^sub>2 v]) # map (\<lambda>tw. (Suc (get_time tw), snd tw)) ws))"
      using 0 by auto
    hence "event_of (Irwline (Adv x2) ((n, snd tw[ sig, dly :=\<^sub>2 v]) # ws) ) = event_of (Irwline (Adv x2) ((n, snd tw) # ws)) \<union> {sig} \<or>
           event_of (Irwline (Adv x2) ((n, snd tw[ sig, dly :=\<^sub>2 v]) # ws) ) = event_of (Irwline (Adv x2) ((n, snd tw) # ws)) - {sig}"
      using Adv * by auto
    then show ?case 
      by auto
  qed
  hence "event_of (Irwline x2 (tw [ sig, dly :=\<^sub>2 v] # ws)) = (event_of (Irwline x2 (tw # ws)) \<union> {sig}) \<or> 
         event_of (Irwline x2 (tw [ sig, dly :=\<^sub>2 v] # ws)) = event_of (Irwline x2 (tw # ws)) - {sig}"
    using surjective_pairing  by (metis fst_worldline_upd2)
  moreover
  { assume \<open>event_of (Irwline x2 (tw [ sig, dly :=\<^sub>2 v] # ws)) = (event_of (Irwline x2 (tw # ws)) \<union> {sig}) \<close>
    hence ?thesis
      using assms \<open>sig \<notin> Irset x1 ss\<close> by auto
  }
  moreover
  { assume \<open>event_of (Irwline x2 (tw [ sig, dly :=\<^sub>2 v] # ws)) = event_of (Irwline x2 (tw # ws)) - {sig}\<close>
    hence ?thesis
      using assms \<open>sig \<notin> Irset x1 ss\<close> 
      by (metis (no_types, lifting) Diff_empty Diff_insert0 disjnt_insert2 insert_Diff)
  }
  ultimately show ?thesis
    by blast
qed


lemma event_of_worldline_inert_upd2:
  "event_of (n, snd tw\<lbrakk> sig, dly :=\<^sub>2 v\<rbrakk>) = event_of (n, snd tw) - {sig} \<or>  (event_of (n, snd tw\<lbrakk> sig, dly :=\<^sub>2 v\<rbrakk>) = event_of (n, snd tw) \<union> {sig})"
proof (induction n)
  case 0
  have " event_of (0, snd tw\<lbrakk> sig, dly :=\<^sub>2 v\<rbrakk>) = {s. snd (snd tw\<lbrakk> sig, dly :=\<^sub>2 v\<rbrakk>) s 0 \<noteq> fst (snd tw) s}" (is "_ = ?rhs")
    unfolding event_of_alt_def by (auto simp add: worldline_inert_upd2_def worldline_inert_upd_def)
  have "fst (snd tw) sig = snd (snd tw \<lbrakk>sig, dly :=\<^sub>2 v\<rbrakk>) sig 0 \<or> fst (snd tw) sig \<noteq> snd (snd tw \<lbrakk>sig, dly :=\<^sub>2 v\<rbrakk>) sig 0"
    by auto
  moreover
  { assume "fst (snd tw) sig = snd (snd tw \<lbrakk>sig, dly :=\<^sub>2 v\<rbrakk>) sig 0"
    hence *: "sig \<notin> {s. snd (snd tw\<lbrakk> sig, dly :=\<^sub>2 v\<rbrakk>) s 0 \<noteq> fst (snd tw) s}"
      by auto
    have **: "\<And>s. s \<noteq> sig \<Longrightarrow> snd (snd tw\<lbrakk> sig, dly :=\<^sub>2 v\<rbrakk>) s 0 = snd (snd tw) s 0"
      unfolding worldline_inert_upd2_def worldline_inert_upd_def by auto
    have "{s. snd (snd tw\<lbrakk> sig, dly :=\<^sub>2 v\<rbrakk>) s 0 \<noteq> fst (snd tw) s} = 
          {s. s = sig \<and> snd (snd tw\<lbrakk> sig, dly :=\<^sub>2 v\<rbrakk>) s 0 \<noteq> fst (snd tw) s} \<union> {s. s \<noteq> sig \<and> snd (snd tw\<lbrakk> sig, dly :=\<^sub>2 v\<rbrakk>) s 0 \<noteq> fst (snd tw) s}"
      using Collect_disj_eq by blast
    also have "... = {s. s \<noteq> sig \<and> snd (snd tw\<lbrakk> sig, dly :=\<^sub>2 v\<rbrakk>) s 0 \<noteq> fst (snd tw) s}"
      using * by auto
    also have "... = {s. s \<noteq> sig \<and> snd (snd tw) s 0 \<noteq> fst (snd tw) s}"
      using ** by auto
    also have "... = {s. snd (snd tw) s 0 \<noteq> fst (snd tw) s} - {sig}"
      by auto 
    also have "... = event_of (0, snd tw) - {sig}"
      unfolding event_of_alt_def by auto
    finally have "event_of (0, snd tw\<lbrakk> sig, dly :=\<^sub>2 v\<rbrakk>) = event_of (0, snd tw) - {sig}"
      by (simp add: \<open>event_of (0, snd tw\<lbrakk> sig, dly :=\<^sub>2 v\<rbrakk>) = {s. snd (snd tw\<lbrakk> sig, dly :=\<^sub>2 v\<rbrakk>) s 0 \<noteq> get_time (snd tw) s}\<close>) }
  moreover
  { assume "fst (snd tw) sig \<noteq> snd (snd tw \<lbrakk>sig, dly :=\<^sub>2 v\<rbrakk>) sig 0"
    hence *: "sig \<in> {s. snd (snd tw\<lbrakk> sig, dly :=\<^sub>2 v\<rbrakk>) s 0 \<noteq> fst (snd tw) s}"
      by auto
    have **: "\<And>s. s \<noteq> sig \<Longrightarrow> snd (snd tw\<lbrakk> sig, dly :=\<^sub>2 v\<rbrakk>) s 0 = snd (snd tw) s 0"
      unfolding worldline_inert_upd2_def worldline_inert_upd_def by auto
    have "{s. snd (snd tw\<lbrakk> sig, dly :=\<^sub>2 v\<rbrakk>) s 0 \<noteq> fst (snd tw) s} = 
          {s. s = sig \<and> snd (snd tw\<lbrakk> sig, dly :=\<^sub>2 v\<rbrakk>) s 0 \<noteq> fst (snd tw) s} \<union> {s. s \<noteq> sig \<and> snd (snd tw\<lbrakk> sig, dly :=\<^sub>2 v\<rbrakk>) s 0 \<noteq> fst (snd tw) s}"
      using Collect_disj_eq by blast
    also have "... = {sig} \<union> {s. s \<noteq> sig \<and> snd (snd tw\<lbrakk> sig, dly :=\<^sub>2 v\<rbrakk>) s 0 \<noteq> fst (snd tw) s}"
      using * by auto
    also have "... = {s. s \<noteq> sig \<and> snd (snd tw) s 0 \<noteq> fst (snd tw) s} \<union> {sig}"
      using ** by auto
    also have "... = {s. snd (snd tw) s 0 \<noteq> fst (snd tw) s} \<union> {sig}"
      by auto
    also have "... = event_of (0, snd tw) \<union> {sig}"
      unfolding event_of_alt_def by auto
    finally have "event_of (0, snd tw\<lbrakk> sig, dly :=\<^sub>2 v\<rbrakk>) = event_of (0, snd tw) \<union> {sig}"
      by (simp add: \<open>event_of (0, snd tw\<lbrakk> sig, dly :=\<^sub>2 v\<rbrakk>) = {s. snd (snd tw\<lbrakk> sig, dly :=\<^sub>2 v\<rbrakk>) s 0 \<noteq> get_time (snd tw) s}\<close>) }
  ultimately show ?case 
    by auto
next
  case (Suc n)
  have " event_of (Suc n, snd tw\<lbrakk> sig, dly :=\<^sub>2 v\<rbrakk>) =  {s. snd ( snd tw\<lbrakk> sig, dly :=\<^sub>2 v\<rbrakk>) s (Suc n) \<noteq> snd (snd tw\<lbrakk> sig, dly :=\<^sub>2 v\<rbrakk>) s n}"
    unfolding event_of_alt_def by auto
  have "snd ( snd tw\<lbrakk> sig, dly :=\<^sub>2 v\<rbrakk>) sig (Suc n) \<noteq> snd (snd tw\<lbrakk> sig, dly :=\<^sub>2 v\<rbrakk>) sig n \<or> 
        snd ( snd tw\<lbrakk> sig, dly :=\<^sub>2 v\<rbrakk>) sig (Suc n) = snd (snd tw\<lbrakk> sig, dly :=\<^sub>2 v\<rbrakk>) sig n"
    by auto
  moreover
  { assume "snd ( snd tw\<lbrakk> sig, dly :=\<^sub>2 v\<rbrakk>) sig (Suc n) = snd (snd tw\<lbrakk> sig, dly :=\<^sub>2 v\<rbrakk>) sig n"
    hence *: "sig \<notin> {s. snd ( snd tw\<lbrakk> sig, dly :=\<^sub>2 v\<rbrakk>) s (Suc n) \<noteq> snd (snd tw\<lbrakk> sig, dly :=\<^sub>2 v\<rbrakk>) s n}"
      by auto
    have **: "\<And>s k. s \<noteq> sig \<Longrightarrow> snd (snd tw\<lbrakk> sig, dly :=\<^sub>2 v\<rbrakk>) s k = snd (snd tw) s k"
      unfolding worldline_inert_upd2_def worldline_inert_upd_def by auto
    have "{s. snd ( snd tw\<lbrakk> sig, dly :=\<^sub>2 v\<rbrakk>) s (Suc n) \<noteq> snd (snd tw\<lbrakk> sig, dly :=\<^sub>2 v\<rbrakk>) s n} = 
          {s. s = sig \<and> snd ( snd tw\<lbrakk> sig, dly :=\<^sub>2 v\<rbrakk>) s (Suc n) \<noteq> snd (snd tw\<lbrakk> sig, dly :=\<^sub>2 v\<rbrakk>) s n} \<union> {s. s \<noteq> sig \<and> snd ( snd tw\<lbrakk> sig, dly :=\<^sub>2 v\<rbrakk>) s (Suc n) \<noteq> snd (snd tw\<lbrakk> sig, dly :=\<^sub>2 v\<rbrakk>) s n}"  
      by auto
    also have "... = {s. s \<noteq> sig \<and> snd ( snd tw\<lbrakk> sig, dly :=\<^sub>2 v\<rbrakk>) s (Suc n) \<noteq> snd (snd tw\<lbrakk> sig, dly :=\<^sub>2 v\<rbrakk>) s n}"
      using * by auto
    also have "... = {s. s \<noteq> sig \<and> snd (snd tw) s (Suc n) \<noteq> snd (snd tw) s n}"
      using ** by auto
    also have "... = {s. snd (snd tw) s (Suc n) \<noteq> snd (snd tw) s n} - {sig}"
      by auto
    also have "... = event_of (Suc n, snd tw) - {sig}"
      unfolding event_of_alt_def by auto
    finally have "event_of (Suc n, snd tw\<lbrakk> sig, dly :=\<^sub>2 v\<rbrakk>) = event_of (Suc n, snd tw) - {sig}"
      by (simp add: \<open>event_of (Suc n, snd tw\<lbrakk> sig, dly :=\<^sub>2 v\<rbrakk>) = {s. snd (snd tw\<lbrakk> sig, dly :=\<^sub>2 v\<rbrakk>) s (Suc n) \<noteq> snd (snd tw\<lbrakk> sig, dly :=\<^sub>2 v\<rbrakk>) s n}\<close>) }
  moreover
  { assume "snd ( snd tw\<lbrakk> sig, dly :=\<^sub>2 v\<rbrakk>) sig (Suc n) \<noteq> snd (snd tw\<lbrakk> sig, dly :=\<^sub>2 v\<rbrakk>) sig n"
    hence *: "sig \<in> {s. snd ( snd tw\<lbrakk> sig, dly :=\<^sub>2 v\<rbrakk>) s (Suc n) \<noteq> snd (snd tw\<lbrakk> sig, dly :=\<^sub>2 v\<rbrakk>) s n}"
      by auto    
    have **: "\<And>s k. s \<noteq> sig \<Longrightarrow> snd (snd tw\<lbrakk> sig, dly :=\<^sub>2 v\<rbrakk>) s k = snd (snd tw) s k"
      unfolding worldline_inert_upd2_def worldline_inert_upd_def by auto    
    have "{s. snd ( snd tw\<lbrakk> sig, dly :=\<^sub>2 v\<rbrakk>) s (Suc n) \<noteq> snd (snd tw\<lbrakk> sig, dly :=\<^sub>2 v\<rbrakk>) s n} = 
          {s. s = sig \<and> snd ( snd tw\<lbrakk> sig, dly :=\<^sub>2 v\<rbrakk>) s (Suc n) \<noteq> snd (snd tw\<lbrakk> sig, dly :=\<^sub>2 v\<rbrakk>) s n} \<union> {s. s \<noteq> sig \<and> snd ( snd tw\<lbrakk> sig, dly :=\<^sub>2 v\<rbrakk>) s (Suc n) \<noteq> snd (snd tw\<lbrakk> sig, dly :=\<^sub>2 v\<rbrakk>) s n}"  
      by auto
    also have "... = {sig} \<union> {s. s \<noteq> sig \<and> snd ( snd tw\<lbrakk> sig, dly :=\<^sub>2 v\<rbrakk>) s (Suc n) \<noteq> snd (snd tw\<lbrakk> sig, dly :=\<^sub>2 v\<rbrakk>) s n}"
      using * by auto
    also have "... = {sig} \<union> {s. s \<noteq> sig \<and> snd (snd tw) s (Suc n) \<noteq> snd (snd tw) s n}"
      using ** by auto
    also have "... = event_of (Suc n, snd tw) \<union> {sig}"
      unfolding event_of_alt_def by auto
    finally have "event_of (Suc n, snd tw\<lbrakk> sig, dly :=\<^sub>2 v\<rbrakk>) = event_of (Suc n, snd tw) \<union> {sig}"
      by (simp add: \<open>event_of (Suc n, snd tw\<lbrakk> sig, dly :=\<^sub>2 v\<rbrakk>) = {s. snd (snd tw\<lbrakk> sig, dly :=\<^sub>2 v\<rbrakk>) s (Suc n) \<noteq> snd (snd tw\<lbrakk> sig, dly :=\<^sub>2 v\<rbrakk>) s n}\<close>) }
  ultimately show ?case 
    by auto
qed

lemma disjnt_free_vars_inert:
  assumes \<open>sig \<notin> set ss\<close> and \<open>wf_rset_sig x1 (length ss) m\<close> and \<open>highest_rwline_idx x2 \<le> length ws + 1\<close>
  shows \<open>disjnt (Irset x1 ss) (event_of (Irwline x2 (tw\<lbrakk> sig, dly :=\<^sub>2 v\<rbrakk> # ws))) = 
         disjnt (Irset x1 ss) (event_of (Irwline x2 (tw # ws)))\<close>
proof -
  have "sig \<notin> Irset x1 ss"
    using assms
  proof (induction x1)
    case LEmpty
    then show ?case by auto
  next
    case (LCons x11 x12)
    then show ?case 
      by (induction x11) auto
  qed
  have "\<And>n.  
            (event_of (Irwline x2 ((n, snd tw \<lbrakk> sig, dly :=\<^sub>2 v\<rbrakk>) # ws)) = event_of (Irwline x2 ((n, snd tw) # ws)) \<union> {sig}) \<or> 
            (event_of (Irwline x2 ((n, snd tw \<lbrakk> sig, dly :=\<^sub>2 v\<rbrakk>) # ws)) = event_of (Irwline x2 ((n, snd tw) # ws)) - {sig})"
    using assms(3)
  proof (induction x2 arbitrary: ws )
    case (Wvar xa)
    then show ?case 
    proof (induction xa)
      case 0
      then show ?case 
        using event_of_worldline_inert_upd2[where n="n" and tw="tw" and sig="sig" and dly="dly" and v="v"]
        by auto
    next
      case (Suc xa)
      then show ?case by auto
    qed
  next
    case (Adv x2)
    hence " Irwline (Adv x2) ((n, snd tw\<lbrakk> sig, dly :=\<^sub>2 v\<rbrakk>) # ws) = Irwline x2 (map (\<lambda>tw. (Suc (get_time tw), snd tw)) ((n, snd tw\<lbrakk> sig, dly :=\<^sub>2 v\<rbrakk>) # ws))"
      using Irwline_adv_alt_def by fastforce
    also have "... = Irwline x2 ((n + 1, snd tw\<lbrakk>sig, dly :=\<^sub>2 v\<rbrakk>) # map (\<lambda>tw. (Suc (get_time tw), snd tw)) ws)"
      by auto
    finally have 0: "Irwline (Adv x2) ((n, snd tw\<lbrakk> sig, dly :=\<^sub>2 v\<rbrakk>) # ws) = Irwline x2 ((n + 1, snd tw\<lbrakk>sig, dly :=\<^sub>2 v\<rbrakk>) # map (\<lambda>tw. (Suc (get_time tw), snd tw)) ws)"
      by auto
    have "Irwline (Adv x2) ((n, snd tw) # ws) = Irwline x2 (map (\<lambda>tw. (Suc (fst tw),  snd tw)) ((n, snd tw) # ws))"
      using Adv Irwline_adv_alt_def by fastforce
    hence *: "Irwline (Adv x2) ((n, snd tw) # ws) = Irwline x2 ((n + 1, snd tw) # map (\<lambda>tw. (Suc (fst tw),  snd tw)) ws)"
      by auto
    hence "event_of (Irwline (Adv x2) ((n, snd tw\<lbrakk> sig, dly :=\<^sub>2 v\<rbrakk>) # ws) ) = 
           event_of (Irwline x2 ((n + 1, snd tw\<lbrakk>sig, dly :=\<^sub>2 v\<rbrakk>) # map (\<lambda>tw. (Suc (get_time tw), snd tw)) ws))"
      using 0 by auto
    hence "event_of (Irwline (Adv x2) ((n, snd tw\<lbrakk> sig, dly :=\<^sub>2 v\<rbrakk>) # ws) ) = event_of (Irwline (Adv x2) ((n, snd tw) # ws)) \<union> {sig} \<or>
           event_of (Irwline (Adv x2) ((n, snd tw\<lbrakk> sig, dly :=\<^sub>2 v\<rbrakk>) # ws) ) = event_of (Irwline (Adv x2) ((n, snd tw) # ws)) - {sig}"
      using Adv * by auto
    then show ?case 
      by auto
  qed
  hence "event_of (Irwline x2 (tw \<lbrakk> sig , dly :=\<^sub>2 v\<rbrakk> # ws)) = (event_of (Irwline x2 (tw # ws)) \<union> {sig}) \<or> 
         event_of (Irwline x2 (tw \<lbrakk> sig , dly :=\<^sub>2 v\<rbrakk> # ws)) = event_of (Irwline x2 (tw # ws)) - {sig}"
    using surjective_pairing  by (metis snd_conv worldline_inert_upd2_def)
  moreover
  { assume \<open>event_of (Irwline x2 (tw \<lbrakk> sig , dly :=\<^sub>2 v\<rbrakk> # ws)) = (event_of (Irwline x2 (tw # ws)) \<union> {sig}) \<close>
    hence ?thesis
      using assms \<open>sig \<notin> Irset x1 ss\<close> by auto }
  moreover
  { assume \<open>event_of (Irwline x2 (tw \<lbrakk> sig , dly :=\<^sub>2 v\<rbrakk> # ws)) = event_of (Irwline x2 (tw # ws)) - {sig}\<close>
    hence ?thesis
      using assms \<open>sig \<notin> Irset x1 ss\<close> 
      by (metis (no_types, lifting) Diff_empty Diff_insert0 disjnt_insert2 insert_Diff) }
  ultimately show ?thesis
    by blast
qed 


lemma Irint_free_vars:
  assumes \<open>sig \<notin> set ss\<close> \<open>wf_rint_sig x1 (length ss) m\<close>
  shows \<open>Irint x1 (tw[ sig, dly :=\<^sub>2 v] # ws) ss ns = Irint x1 (tw # ws) ss ns\<close>
  using assms
proof  (induction x1)
  case (IC x)
  then show ?case by auto
next
  case (IAdd x11 x12)
  then show ?case by auto
next
  case (IMult x11 x12)
  then show ?case by auto
next
  case (INeg x1)
  then show ?case by auto
next
  case (ISub x11 x12)
  then show ?case by auto
next
  case (Ibin_of x)
  then show ?case 
    by (auto simp add: Irval_free_vars)
next
  case (Isbintrunc x1a x1)
  then show ?case 
    by (auto simp add : Irnat_worldline_upd2)
next
  case (Islice x1a x2 x3)
  then show ?case 
    by (auto simp add : Irnat_worldline_upd2 Irval_free_vars)
next
  case (Iubin_of x)
  then show ?case 
    by (auto simp add: Irval_free_vars)
next
  case (Ibintrunc x1a x1)
  then show ?case 
    by (auto simp add : Irnat_worldline_upd2)
qed

lemma Irint_free_vars_inert:
  assumes \<open>sig \<notin> set ss\<close> \<open>wf_rint_sig x1 (length ss) m\<close>
  shows \<open>Irint x1 (tw\<lbrakk>sig, dly :=\<^sub>2 v\<rbrakk> # ws) ss ns = Irint x1 (tw # ws) ss ns\<close>
  using assms
proof  (induction x1)
  case (IC x)
  then show ?case by auto
next
  case (IAdd x11 x12)
  then show ?case by auto
next
  case (IMult x11 x12)
  then show ?case by auto
next
  case (INeg x1)
  then show ?case by auto
next
  case (ISub x11 x12)
  then show ?case by auto
next
  case (Ibin_of x)
  then show ?case 
    by (auto simp add: Irval_free_vars_inert)
next
  case (Isbintrunc x1a x1)
  then show ?case 
    by (auto simp add : Irnat_worldline_inert_upd2)
next
  case (Islice x1a x2 x3)
  then show ?case 
    by (auto simp add : Irnat_worldline_inert_upd2 Irval_free_vars_inert)
next
  case (Iubin_of x)
  then show ?case 
    by (auto simp add: Irval_free_vars_inert)
next
  case (Ibintrunc x1a x1)
  then show ?case 
    by (auto simp add : Irnat_worldline_inert_upd2)
qed

lemma eval_free_vars:
  assumes \<open>sig \<notin> set ss\<close> and \<open>wf_form_sig Q (length ss) 0\<close> and \<open>highest_idx_form_rwline Q \<le> length ws + 1\<close>
  shows   \<open>eval Q (tw[sig, dly :=\<^sub>2 v] # ws) ns ss = eval Q (tw # ws) ns ss\<close>
  using assms
proof (induction Q arbitrary: ns ss tw ws sig dly v)
  case RF
  then show ?case by auto
next
  case RT
  then show ?case by auto
next
  case (RElof x1 x2)
  then show ?case by auto
next
  case (RNLT x1 x2)
  then show ?case by (auto simp add: Irnat_worldline_upd2)
next
  case (RBval x)
  hence "wf_rval_sig x (length ss) 0"
    by auto
  then show ?case
    using Irval_free_vars RBval(1)  by (metis eval_simps(5))
next
  case (RDisevt x1 x2)
  hence "wf_rset_sig x1 (length ss) 0" and "highest_rwline_idx x2 \<le> length ws + 1"
    by auto
  then show ?case 
    by (auto simp add: disjnt_free_vars RDisevt)
next
  case (RAnd Q1 Q2)
  then show ?case by auto
next
  case (ROr Q1 Q2)
  then show ?case by auto
next
  case (RImp Q1 Q2)
  then show ?case by auto
next
  case (RBImp Q1 Q2)
  then show ?case by auto
next
  case (Rnot Q)
  then show ?case by auto
next
  case (RSigex col Q)
  hence "wf_form_sig Q (length ss + 1) 0"
    unfolding wf_form_sig.simps by auto
  have "highest_idx_form_rwline Q \<le> length ws + 1"
    using RSigex by auto
  have "wf_rset_sig col (length ss + 1) 1"
    using RSigex by auto
  hence *: "\<forall>s. s \<in> Irset col (s # ss) \<longrightarrow> s \<in> set ss"
  proof (induction col)
    case LEmpty
    then show ?case by auto
  next
    case (LCons x1 col)
    hence *: "\<forall>s. s \<in> Irset col (s # ss) \<longrightarrow> s \<in> set ss"
      by auto
    { fix s 
      assume "s \<in> Irset (LCons x1 col) (s # ss)"
      hence "s = Irsig x1 (s # ss) \<or> s \<in> Irset col (s # ss)"
        by auto
      moreover
      { assume "s \<in> Irset col (s # ss)"
        with * have "s \<in> set ss"
          by auto }
      moreover
      { assume "s = Irsig x1 (s # ss)"
        hence "s \<in> set ss"
          using LCons(2) by (induction x1) auto }
      ultimately have "s \<in> set ss" by auto }
    then show ?case 
      by auto
  qed
  show ?case 
    apply simp
  proof 
    assume "\<exists>s. s \<in> Irset col (s # ss) \<and> eval Q (tw[ sig, dly :=\<^sub>2 v] # ws) ns (s # ss)"
    then obtain s where obt1: "s \<in> Irset col (s # ss)" and obt2: "eval Q (tw[ sig, dly :=\<^sub>2 v] # ws) ns (s # ss)"
      by auto
    hence "s \<in> set ss"
      using * by auto
    hence "sig \<notin> set (s # ss)"
      using \<open>sig \<notin> set ss\<close> by auto      
    with RSigex(1)[OF this] and `wf_form_sig Q (length ss + 1) 0`
    have " eval Q (tw[ sig, dly :=\<^sub>2 v] # ws) ns (s # ss) = eval Q (tw # ws) ns (s # ss)"
      by (metis Suc_eq_plus1 \<open>highest_idx_form_rwline Q \<le> length ws + 1\<close> length_Cons)
    thus "\<exists>s. s \<in> Irset col (s # ss) \<and> eval Q (tw # ws) ns (s # ss)"
      using obt1 obt2 by auto
  next
    assume "\<exists>s. s \<in> Irset col (s # ss) \<and> eval Q (tw # ws) ns (s # ss)"
    then obtain s where obt1: "s \<in> Irset col (s # ss)" and obt2: "eval Q (tw # ws) ns (s # ss)"
      by auto
    hence "s \<in> set ss"
      using * by auto
    hence "sig \<notin> set (s # ss)"
      using \<open>sig \<notin> set ss\<close> by auto      
    with RSigex(1)[OF this] have "eval Q (tw[ sig, dly :=\<^sub>2 v] # ws) ns (s # ss) = eval Q (tw # ws) ns (s # ss)"    
      using `wf_form_sig Q (length ss + 1) 0` \<open>highest_idx_form_rwline Q \<le> length ws + 1\<close> by auto
    thus "\<exists>s. s \<in> Irset col (s # ss) \<and> eval Q (tw[ sig, dly :=\<^sub>2 v] # ws) ns (s # ss)"
      using obt1 obt2 by auto
  qed
next
  case (RNex Q)
  then show ?case by auto
next
  case (RSigall col Q)
  hence "wf_form_sig Q (length ss + 1) 0"
    unfolding wf_form_sig.simps by auto
  have "highest_idx_form_rwline Q \<le> length ws + 1"
    using RSigall by auto
  have "wf_rset_sig col (length ss + 1) 1"
    using RSigall by auto
  hence *: "\<forall>s. s \<in> Irset col (s # ss) \<longrightarrow> s \<in> set ss"
  proof (induction col)
    case LEmpty
    then show ?case by auto
  next
    case (LCons x1 col)
    hence *: "\<forall>s. s \<in> Irset col (s # ss) \<longrightarrow> s \<in> set ss"
      by auto
    { fix s 
      assume "s \<in> Irset (LCons x1 col) (s # ss)"
      hence "s = Irsig x1 (s # ss) \<or> s \<in> Irset col (s # ss)"
        by auto
      moreover
      { assume "s \<in> Irset col (s # ss)"
        with * have "s \<in> set ss"
          by auto }
      moreover
      { assume "s = Irsig x1 (s # ss)"
        hence "s \<in> set ss"
          using LCons(2) by (induction x1) auto }
      ultimately have "s \<in> set ss" by auto }
    then show ?case 
      by auto
  qed
  show ?case 
    apply simp
  proof 
    assume **: "\<forall>s. s \<in> Irset col (s # ss) \<longrightarrow> eval Q (tw[ sig, dly :=\<^sub>2 v] # ws) ns (s # ss)"
    show "\<forall>s. s \<in> Irset col (s # ss) \<longrightarrow> eval Q (tw # ws) ns (s # ss)"
    proof (rule, rule)
      fix s 
      assume "s \<in> Irset col (s # ss)"
      with * have "s \<in> set ss"
        by auto
      hence "sig \<notin> set (s # ss)"
        using \<open>sig \<notin> set ss\<close> by auto     
      with RSigall(1)[OF this] have "eval Q (tw[ sig, dly :=\<^sub>2 v] # ws) ns (s # ss) = eval Q (tw # ws) ns (s # ss)"    
        using `wf_form_sig Q (length ss + 1) 0` \<open>highest_idx_form_rwline Q \<le> length ws + 1\<close> by auto
      thus " eval Q (tw # ws) ns (s # ss)"
        using ** `s \<in> Irset col (s # ss)` by blast
    qed
  next
    assume **: "\<forall>s. s \<in> Irset col (s # ss) \<longrightarrow> eval Q (tw # ws) ns (s # ss)"
    show "\<forall>s. s \<in> Irset col (s # ss) \<longrightarrow> eval Q (tw[ sig, dly :=\<^sub>2 v] # ws) ns (s # ss)"
    proof (rule, rule)
      fix s 
      assume "s \<in> Irset col (s # ss)"
      with * have "s \<in> set ss"
        by auto
      hence "sig \<notin> set (s # ss)"
        using \<open>sig \<notin> set ss\<close> by auto     
      with RSigall(1)[OF this] have "eval Q (tw[ sig, dly :=\<^sub>2 v] # ws) ns (s # ss) = eval Q (tw # ws) ns (s # ss)"    
        using `wf_form_sig Q (length ss + 1) 0` \<open>highest_idx_form_rwline Q \<le> length ws + 1\<close> by auto
      thus " eval Q (tw[ sig, dly :=\<^sub>2 v] # ws) ns (s # ss)"
        using ** `s \<in> Irset col (s # ss)` by blast
    qed  
  qed
next
  case (RNall Q)
  then show ?case  by auto
next
  case (RVEq x1 x2)
  then show ?case 
    by (auto simp add: Irval_free_vars)
next
  case (RIfte Q1 Q2 Q3)
  then show ?case  by auto
next
  case (RIEq x1 x2)
  then show ?case 
    by (auto simp add : Irint_free_vars)
next
  case (RILT x1 x2)
  then show ?case 
    by (auto simp add : Irint_free_vars)
next
  case (Rsepand Q1 Q2)
  hence **: "( wf_form_sig Q1 (highest_idx_form_sig Q1) 0 \<and> wf_form_sig Q2 (length ss - (highest_idx_form_sig Q1)) 0)" and "(highest_idx_form_sig Q1) \<le> length ss"
    and "highest_idx_form_rwline Q2 \<le> length ws + 1" and "highest_idx_form_rwline Q1 \<le> length ws + 1"
    by auto
  have *: " eval (Rsepand Q1 Q2) (tw[ sig, dly :=\<^sub>2 v] # ws) ns ss = 
    (eval Q1 (tw[ sig, dly :=\<^sub>2 v] # ws) (take (highest_idx_form_nat Q1) ns) (take (highest_idx_form_sig Q1) ss) \<and> 
     eval Q2 (tw[ sig, dly :=\<^sub>2 v] # ws) (drop (highest_idx_form_nat Q1) ns) (drop (highest_idx_form_sig Q1) ss))"
    unfolding eval.simps by auto
  have notsig1: "sig \<notin> set (take (highest_idx_form_sig Q1) ss)" and notsig2: "sig \<notin> set (drop (highest_idx_form_sig Q1) ss)"
      using Rsepand(3) by (meson in_set_takeD in_set_dropD)+
  have "highest_idx_form_rwline Q1 = 0 \<or> highest_idx_form_rwline Q1 = 1 \<or> 2 \<le> highest_idx_form_rwline Q1"
    by auto
  moreover
  { assume h0: "highest_idx_form_rwline Q1 = 0"
    have h1: "eval (Rsepand Q1 Q2) (tw[ sig, dly :=\<^sub>2 v] # ws) ns ss \<longleftrightarrow>  eval Q1 (tw [sig, dly :=\<^sub>2 v] # ws) (take (highest_idx_form_nat Q1) ns) (take (highest_idx_form_sig Q1) ss) 
                                                                  \<and> eval Q2 (tw [sig, dly :=\<^sub>2 v] # ws) (drop (highest_idx_form_nat Q1) ns) (drop (highest_idx_form_sig Q1) ss)"
      using * unfolding h0 take_0 drop_0 by auto
    hence h2: " eval Q2 (tw [sig, dly :=\<^sub>2 v] # ws) (drop (highest_idx_form_nat Q1) ns) (drop (highest_idx_form_sig Q1) ss) 
          = eval Q2 (tw # ws) (drop (highest_idx_form_nat Q1) ns) (drop (highest_idx_form_sig Q1) ss)"
      using Rsepand(2)[OF notsig2] ** unfolding length_drop 
      using \<open>highest_idx_form_rwline Q2 \<le> length ws + 1\<close> by blast
    have h3: " eval Q1 (tw [sig, dly :=\<^sub>2 v] # ws) (take (highest_idx_form_nat Q1) ns) (take (highest_idx_form_sig Q1) ss) 
          = eval Q1 (tw # ws) (take (highest_idx_form_nat Q1) ns) (take (highest_idx_form_sig Q1) ss)"
      using Rsepand(1)[OF notsig1] **  by (simp add: \<open>highest_idx_form_sig Q1 \<le> length ss\<close> h0 min.absorb2)
    have "eval (Rsepand Q1 Q2) (tw # ws) ns ss \<longleftrightarrow> eval Q1 (tw # ws) (take (highest_idx_form_nat Q1) ns) (take (highest_idx_form_sig Q1) ss)
                                                 \<and> eval Q2 (tw # ws) (drop (highest_idx_form_nat Q1) ns) (drop (highest_idx_form_sig Q1) ss)"
      unfolding eval.simps h0 take_0 drop_0 by auto
    hence ?case
      using h1 h2 h3 by blast }
  moreover
  { assume h0: "highest_idx_form_rwline Q1 = 1"
    hence "eval (Rsepand Q1 Q2) (tw[ sig, dly :=\<^sub>2 v] # ws) ns ss \<longleftrightarrow>  eval Q1 (tw[ sig, dly :=\<^sub>2 v] # ws) (take (highest_idx_form_nat Q1) ns) (take (highest_idx_form_sig Q1) ss) 
                                                                  \<and> eval Q2 (tw[ sig, dly :=\<^sub>2 v] # ws) (drop (highest_idx_form_nat Q1) ns) (drop (highest_idx_form_sig Q1) ss)"
      by simp
    hence ?case
      apply simp
      by (metis (no_types, lifting) "**" Rsepand.IH(1) Rsepand.IH(2) \<open>highest_idx_form_rwline Q2 \<le>
      length ws + 1\<close> \<open>highest_idx_form_sig Q1 \<le> length ss\<close> eval.simps(18) h0 le_add2 length_drop
      length_take min.absorb2 notsig1 notsig2) }
  moreover
  { assume "2 \<le> highest_idx_form_rwline Q1"
    hence "eval (Rsepand Q1 Q2) (tw[ sig, dly :=\<^sub>2 v] # ws) ns ss \<longleftrightarrow>  
            eval Q1 (tw[ sig, dly :=\<^sub>2 v] # ws) (take (highest_idx_form_nat Q1) ns) (take (highest_idx_form_sig Q1) ss) 
          \<and> eval Q2 (tw[ sig, dly :=\<^sub>2 v] # ws) (drop (highest_idx_form_nat Q1) ns) (drop (highest_idx_form_sig Q1) ss)"
      by auto
    hence ?case
      apply simp
      by (metis (no_types, lifting) "**" Rsepand.IH(1) Rsepand.IH(2) \<open>highest_idx_form_rwline Q1 \<le>
      length ws + 1\<close> \<open>highest_idx_form_rwline Q2 \<le> length ws + 1\<close> \<open>highest_idx_form_sig Q1 \<le> length
      ss\<close> eval.simps(18) length_drop length_take min.absorb2 notsig1 notsig2) }
  ultimately show ?case
    by auto    
qed

lemma eval_free_vars2:
  assumes \<open>sig \<notin> set ss\<close> and \<open>wf_form_sig Q (length ss) 0\<close> and \<open>highest_idx_form_rwline Q \<le> length ws + 1\<close> 
  assumes "sig \<noteq> sig'"
  shows   \<open>eval Q (tw[sig, dly :=\<^sub>2 v][sig', dly' :=\<^sub>2 v'] # ws) ns ss = eval Q (tw[sig', dly' :=\<^sub>2 v'] # ws) ns ss\<close>
  using assms unfolding switch_worldline_upd2[OF `sig \<noteq> sig'`]
  using eval_free_vars[OF assms(1-3)] by auto

lemma eval_free_vars3:
  assumes \<open>sig \<notin> set ss\<close> and \<open>wf_form_sig Q (length ss) 0\<close> and \<open>highest_idx_form_rwline Q \<le> length ws + 1\<close> 
  assumes "sig \<noteq> sig'" and "sig \<noteq> sig''" and "sig' \<noteq> sig''"
  shows   \<open>eval Q (tw[sig, dly :=\<^sub>2 v][sig', dly' :=\<^sub>2 v'][sig'', dly'' :=\<^sub>2 v''] # ws) ns ss = eval Q (tw[sig', dly' :=\<^sub>2 v'][sig'', dly'' :=\<^sub>2 v''] # ws) ns ss\<close>
  using assms  unfolding switch_assignment3[OF assms(4) assms(6) assms(5)]
  using eval_free_vars[OF assms(1-3)] by auto

lemma eval_free_vars_inert:
  assumes \<open>sig \<notin> set ss\<close> and \<open>wf_form_sig Q (length ss) 0\<close> and \<open>highest_idx_form_rwline Q \<le> length ws + 1\<close>
  shows   \<open>eval Q (tw\<lbrakk>sig, dly :=\<^sub>2 v\<rbrakk> # ws) ns ss = eval Q (tw # ws) ns ss\<close>
  using assms
proof (induction Q arbitrary: ns ss tw ws sig dly v)
  case RF
  then show ?case by auto
next
  case RT
  then show ?case by auto
next
  case (RElof x1 x2)
  then show ?case by auto
next
  case (RNLT x1 x2)
  then show ?case by (auto simp add: Irnat_worldline_inert_upd2)
next
  case (RBval x)
  hence "wf_rval_sig x (length ss) 0"
    by auto
  then show ?case
    using Irval_free_vars_inert RBval(1)  by (metis eval_simps(5))
next
  case (RDisevt x1 x2)
  hence "wf_rset_sig x1 (length ss) 0" and "highest_rwline_idx x2 \<le> length ws + 1"
    by auto
  then show ?case 
    by (auto simp add: disjnt_free_vars_inert RDisevt)
next
  case (RAnd Q1 Q2)
  then show ?case by auto
next
  case (ROr Q1 Q2)
  then show ?case by auto
next
  case (RImp Q1 Q2)
  then show ?case by auto
next
  case (RBImp Q1 Q2)
  then show ?case by auto
next
  case (Rnot Q)
  then show ?case by auto
next
  case (RSigex col Q)
  hence "wf_form_sig Q (length ss + 1) 0"
    unfolding wf_form_sig.simps by auto
  have " highest_idx_form_rwline Q \<le> length ws + 1"
    using RSigex by auto
  have "wf_rset_sig col (length ss + 1) 1"
    using RSigex by auto
  hence *: "\<forall>s. s \<in> Irset col (s # ss) \<longrightarrow> s \<in> set ss"
  proof (induction col)
    case LEmpty
    then show ?case by auto
  next
    case (LCons x1 col)
    hence *: "\<forall>s. s \<in> Irset col (s # ss) \<longrightarrow> s \<in> set ss"
      by auto
    { fix s 
      assume "s \<in> Irset (LCons x1 col) (s # ss)"
      hence "s = Irsig x1 (s # ss) \<or> s \<in> Irset col (s # ss)"
        by auto
      moreover
      { assume "s \<in> Irset col (s # ss)"
        with * have "s \<in> set ss"
          by auto }
      moreover
      { assume "s = Irsig x1 (s # ss)"
        hence "s \<in> set ss"
          using LCons(2) by (induction x1) auto }
      ultimately have "s \<in> set ss" by auto }
    then show ?case 
      by auto
  qed
  show ?case 
    apply simp
  proof 
    assume "\<exists>s. s \<in> Irset col (s # ss) \<and> eval Q (tw\<lbrakk> sig, dly :=\<^sub>2 v\<rbrakk> # ws) ns (s # ss)"
    then obtain s where obt1: "s \<in> Irset col (s # ss)" and obt2: "eval Q (tw\<lbrakk> sig, dly :=\<^sub>2 v\<rbrakk> # ws) ns (s # ss)"
      by auto
    hence "s \<in> set ss"
      using * by auto
    hence "sig \<notin> set (s # ss)"
      using \<open>sig \<notin> set ss\<close> by auto      
    with RSigex(1)[OF this] and `wf_form_sig Q (length ss + 1) 0`
    have " eval Q (tw\<lbrakk> sig, dly :=\<^sub>2 v\<rbrakk> # ws) ns (s # ss) = eval Q (tw # ws) ns (s # ss)"
      using \<open>highest_idx_form_rwline Q \<le> length ws + 1\<close> by auto
    thus "\<exists>s. s \<in> Irset col (s # ss) \<and> eval Q (tw # ws) ns (s # ss)"
      using obt1 obt2 by auto
  next
    assume "\<exists>s. s \<in> Irset col (s # ss) \<and> eval Q (tw # ws) ns (s # ss)"
    then obtain s where obt1: "s \<in> Irset col (s # ss)" and obt2: "eval Q (tw # ws) ns (s # ss)"
      by auto
    hence "s \<in> set ss"
      using * by auto
    hence "sig \<notin> set (s # ss)"
      using \<open>sig \<notin> set ss\<close> by auto      
    with RSigex(1)[OF this] have "eval Q (tw\<lbrakk> sig, dly :=\<^sub>2 v\<rbrakk> # ws) ns (s # ss) = eval Q (tw # ws) ns (s # ss)"    
      using `wf_form_sig Q (length ss + 1) 0`  using \<open>highest_idx_form_rwline Q \<le> length ws + 1\<close> by auto
    thus "\<exists>s. s \<in> Irset col (s # ss) \<and> eval Q (tw\<lbrakk> sig, dly :=\<^sub>2 v\<rbrakk> # ws) ns (s # ss)"
      using obt1 obt2 by auto
  qed
next
  case (RNex Q)
  then show ?case by auto
next
  case (RSigall col Q)
  hence "wf_form_sig Q (length ss + 1) 0"
    unfolding wf_form_sig.simps by auto
  have " highest_idx_form_rwline Q \<le> length ws + 1"
    using RSigall by auto
  have "wf_rset_sig col (length ss + 1) 1"
    using RSigall by auto
  hence *: "\<forall>s. s \<in> Irset col (s # ss) \<longrightarrow> s \<in> set ss"
  proof (induction col)
    case LEmpty
    then show ?case by auto
  next
    case (LCons x1 col)
    hence *: "\<forall>s. s \<in> Irset col (s # ss) \<longrightarrow> s \<in> set ss"
      by auto
    { fix s 
      assume "s \<in> Irset (LCons x1 col) (s # ss)"
      hence "s = Irsig x1 (s # ss) \<or> s \<in> Irset col (s # ss)"
        by auto
      moreover
      { assume "s \<in> Irset col (s # ss)"
        with * have "s \<in> set ss"
          by auto }
      moreover
      { assume "s = Irsig x1 (s # ss)"
        hence "s \<in> set ss"
          using LCons(2) by (induction x1) auto }
      ultimately have "s \<in> set ss" by auto }
    then show ?case 
      by auto
  qed
  show ?case 
    apply simp
  proof 
    assume **: "\<forall>s. s \<in> Irset col (s # ss) \<longrightarrow> eval Q (tw\<lbrakk> sig, dly :=\<^sub>2 v\<rbrakk> # ws) ns (s # ss)"
    show "\<forall>s. s \<in> Irset col (s # ss) \<longrightarrow> eval Q (tw # ws) ns (s # ss)"
    proof (rule, rule)
      fix s 
      assume "s \<in> Irset col (s # ss)"
      with * have "s \<in> set ss"
        by auto
      hence "sig \<notin> set (s # ss)"
        using \<open>sig \<notin> set ss\<close> by auto     
      with RSigall(1)[OF this] have "eval Q (tw\<lbrakk> sig, dly :=\<^sub>2 v\<rbrakk> # ws) ns (s # ss) = eval Q (tw # ws) ns (s # ss)"    
        using `wf_form_sig Q (length ss + 1) 0`
        by (metis Suc_eq_plus1 \<open>highest_idx_form_rwline Q \<le> length ws + 1\<close> length_Cons)
      thus " eval Q (tw # ws) ns (s # ss)"
        using ** `s \<in> Irset col (s # ss)` by blast
    qed
  next
    assume **: "\<forall>s. s \<in> Irset col (s # ss) \<longrightarrow> eval Q (tw # ws) ns (s # ss)"
    show "\<forall>s. s \<in> Irset col (s # ss) \<longrightarrow> eval Q (tw\<lbrakk> sig, dly :=\<^sub>2 v\<rbrakk> # ws) ns (s # ss)"
    proof (rule, rule)
      fix s 
      assume "s \<in> Irset col (s # ss)"
      with * have "s \<in> set ss"
        by auto
      hence "sig \<notin> set (s # ss)"
        using \<open>sig \<notin> set ss\<close> by auto     
      with RSigall(1)[OF this] have "eval Q (tw\<lbrakk> sig, dly :=\<^sub>2 v\<rbrakk> # ws) ns (s # ss) = eval Q (tw # ws) ns (s # ss)"    
        using `wf_form_sig Q (length ss + 1) 0` \<open>highest_idx_form_rwline Q \<le> length ws + 1\<close> by auto
      thus " eval Q (tw\<lbrakk> sig, dly :=\<^sub>2 v\<rbrakk> # ws) ns (s # ss)"
        using ** `s \<in> Irset col (s # ss)` by blast
    qed  
  qed
next
  case (RNall Q)
  then show ?case  by auto
next
  case (RVEq x1 x2)
  then show ?case 
    by (auto simp add: Irval_free_vars_inert)
next
  case (RIfte Q1 Q2 Q3)
  then show ?case  by auto
next
  case (RIEq x1 x2)
  then show ?case 
    by (auto simp add : Irint_free_vars_inert)
next
  case (RILT x1 x2)
  then show ?case 
    by (auto simp add : Irint_free_vars_inert)
next
  case (Rsepand Q1 Q2)
  hence **: "( wf_form_sig Q1 (highest_idx_form_sig Q1) 0 \<and> wf_form_sig Q2 (length ss - (highest_idx_form_sig Q1)) 0)" and "(highest_idx_form_sig Q1) \<le> length ss"
    and " highest_idx_form_rwline Q1 \<le> length ws + 1 " and " highest_idx_form_rwline Q2 \<le> length ws + 1 "
    by auto
  have *: " eval (Rsepand Q1 Q2) (tw\<lbrakk> sig, dly :=\<^sub>2 v\<rbrakk> # ws) ns ss = 
    (eval Q1 (tw\<lbrakk> sig, dly :=\<^sub>2 v\<rbrakk> # ws) (take (highest_idx_form_nat Q1) ns) (take (highest_idx_form_sig Q1) ss) \<and> 
     eval Q2 (tw\<lbrakk> sig, dly :=\<^sub>2 v\<rbrakk> # ws) (drop (highest_idx_form_nat Q1) ns) (drop (highest_idx_form_sig Q1) ss))"
    unfolding eval.simps by auto
  have notsig1: "sig \<notin> set (take (highest_idx_form_sig Q1) ss)" and notsig2: "sig \<notin> set (drop (highest_idx_form_sig Q1) ss)"
      using Rsepand(3) by (meson in_set_takeD in_set_dropD)+
  have "highest_idx_form_rwline Q1 = 0 \<or> highest_idx_form_rwline Q1 = 1 \<or> 2 \<le> highest_idx_form_rwline Q1"
    by auto
  moreover
  { assume h0: "highest_idx_form_rwline Q1 = 0"
    have h1: "eval (Rsepand Q1 Q2) (tw\<lbrakk> sig, dly :=\<^sub>2 v\<rbrakk> # ws) ns ss \<longleftrightarrow>  eval Q1 (tw\<lbrakk> sig, dly :=\<^sub>2 v\<rbrakk> # ws) (take (highest_idx_form_nat Q1) ns) (take (highest_idx_form_sig Q1) ss) 
                                                                  \<and> eval Q2 (tw \<lbrakk>sig, dly :=\<^sub>2 v\<rbrakk> # ws) (drop (highest_idx_form_nat Q1) ns) (drop (highest_idx_form_sig Q1) ss)"
      using * unfolding h0 take_0 drop_0 by auto
    hence h2: " eval Q2 (tw \<lbrakk>sig, dly :=\<^sub>2 v\<rbrakk> # ws) (drop (highest_idx_form_nat Q1) ns) (drop (highest_idx_form_sig Q1) ss) 
          = eval Q2 (tw # ws) (drop (highest_idx_form_nat Q1) ns) (drop (highest_idx_form_sig Q1) ss)"
      using Rsepand(2)[OF notsig2] ** unfolding length_drop 
      using \<open>highest_idx_form_rwline Q2 \<le> length ws + 1\<close> by blast
    hence h3: " eval Q1 (tw \<lbrakk>sig, dly :=\<^sub>2 v\<rbrakk> # ws) (take (highest_idx_form_nat Q1) ns) (take (highest_idx_form_sig Q1) ss) 
          = eval Q1 (tw # ws) (take (highest_idx_form_nat Q1) ns) (take (highest_idx_form_sig Q1) ss)"
      using Rsepand(1)[OF notsig1] ** unfolding length_drop 
      by (simp add: \<open>highest_idx_form_sig Q1 \<le> length ss\<close> h0 min.absorb2)
    have "eval (Rsepand Q1 Q2) (tw # ws) ns ss \<longleftrightarrow> eval Q1 (tw # ws) (take (highest_idx_form_nat Q1) ns) (take (highest_idx_form_sig Q1) ss)
                                                 \<and> eval Q2 (tw # ws) (drop (highest_idx_form_nat Q1) ns) (drop (highest_idx_form_sig Q1) ss)"
      unfolding eval.simps h0 take_0 drop_0 by auto
    hence ?case
      using h1 h2 h3 by blast }
  moreover
  { assume h0: "highest_idx_form_rwline Q1 = 1"
    hence "eval (Rsepand Q1 Q2) (tw\<lbrakk> sig, dly :=\<^sub>2 v\<rbrakk> # ws) ns ss \<longleftrightarrow>  eval Q1 (tw\<lbrakk> sig, dly :=\<^sub>2 v\<rbrakk> # ws) (take (highest_idx_form_nat Q1) ns) (take (highest_idx_form_sig Q1) ss) 
                                                                  \<and> eval Q2 (tw\<lbrakk> sig, dly :=\<^sub>2 v\<rbrakk> # ws) (drop (highest_idx_form_nat Q1) ns) (drop (highest_idx_form_sig Q1) ss)"
      by simp
    hence ?case
      by simp(metis (no_types, lifting) "**" Rsepand.IH(1) Rsepand.IH(2) \<open>highest_idx_form_rwline Q1 \<le>
      length ws + 1\<close> \<open>highest_idx_form_rwline Q2 \<le> length ws + 1\<close> \<open>highest_idx_form_sig Q1 \<le> length
      ss\<close> eval.simps(18) length_drop length_take min.absorb2 notsig1 notsig2) }
  moreover
  { assume "2 \<le> highest_idx_form_rwline Q1"
    hence "eval (Rsepand Q1 Q2) (tw\<lbrakk> sig, dly :=\<^sub>2 v\<rbrakk> # ws) ns ss \<longleftrightarrow>  
            eval Q1 (tw\<lbrakk> sig, dly :=\<^sub>2 v\<rbrakk> # ws) (take (highest_idx_form_nat Q1) ns) (take (highest_idx_form_sig Q1) ss) 
          \<and> eval Q2 (tw\<lbrakk> sig, dly :=\<^sub>2 v\<rbrakk> # ws) (drop (highest_idx_form_nat Q1) ns) (drop (highest_idx_form_sig Q1) ss)"
      by (metis (full_types) "*" drop_Cons' le0 le_antisym take_Cons' zero_neq_numeral)
    hence ?case
      by simp (metis (no_types, lifting) "**" Rsepand.IH(1) Rsepand.IH(2) \<open>highest_idx_form_rwline Q1 \<le>
      length ws + 1\<close> \<open>highest_idx_form_rwline Q2 \<le> length ws + 1\<close> \<open>highest_idx_form_sig Q1 \<le> length
      ss\<close> eval.simps(18) length_drop length_take min.absorb2 notsig1 notsig2) }
  ultimately show ?case
    by auto    
qed

lemma eval_free_vars_inert2:
  assumes \<open>sig \<notin> set ss\<close> and \<open>wf_form_sig Q (length ss) 0\<close> and \<open>highest_idx_form_rwline Q \<le> length ws + 1\<close>
  assumes \<open>sig \<noteq> sig'\<close>
  shows   \<open>eval Q (tw\<lbrakk>sig, dly :=\<^sub>2 v\<rbrakk>\<lbrakk>sig', dly' :=\<^sub>2 v'\<rbrakk> # ws) ns ss = eval Q (tw\<lbrakk>sig', dly' :=\<^sub>2 v'\<rbrakk> # ws) ns ss\<close>
  unfolding  switch_worldline_inert_upd2[OF assms(4)]
  using eval_free_vars_inert[OF assms(1-3)]  by auto

lemma eval_free_vars_inert2':
  assumes \<open>sig \<notin> set ss\<close> and \<open>wf_form_sig Q (length ss) 0\<close> and \<open>highest_idx_form_rwline Q \<le> length ws + 1\<close>
  assumes \<open>sig \<noteq> sig'\<close>
  shows   \<open>eval Q (tw\<lbrakk>sig, dly :=\<^sub>2 v\<rbrakk>[sig', dly' :=\<^sub>2 v'] # ws) ns ss = eval Q (tw[sig', dly' :=\<^sub>2 v'] # ws) ns ss\<close>
  unfolding  switch_worldline_inert_non_inert[OF assms(4)]
  using eval_free_vars_inert[OF assms(1-3)]  by auto

lemma eval_free_vars_inert3:
  assumes \<open>sig \<notin> set ss\<close> and \<open>wf_form_sig Q (length ss) 0\<close> and \<open>highest_idx_form_rwline Q \<le> length ws + 1\<close>
  assumes \<open>sig \<noteq> sig'\<close> and "sig' \<noteq> sig''" and "sig \<noteq> sig''"
  shows   \<open>eval Q (tw\<lbrakk>sig, dly :=\<^sub>2 v\<rbrakk>[sig', dly' :=\<^sub>2 v'][sig'', dly'' :=\<^sub>2 v''] # ws) ns ss = eval Q (tw[sig', dly' :=\<^sub>2 v'][sig'', dly'' :=\<^sub>2 v''] # ws) ns ss\<close>
  unfolding switch_worldline_inert_non_inert3[OF assms(4-6)]
  using eval_free_vars_inert[OF assms(1-3)]  by auto

lemma interp_hoare_seq_free_vars:
  assumes \<open>set (signals_in seq) \<inter> set ss = {}\<close>
  assumes \<open>nonneg_delay seq\<close> and \<open>seq_wt \<Gamma> seq\<close>
  assumes \<open>wf_form_sig Q (length ss) 0\<close>
  assumes \<open>highest_idx_form_rwline Q \<le> 1\<close>
  shows   \<open>interp_hoare_seq (Hoare (Abs Q) (Abs Q)) ns ss ns ss \<Gamma> seq\<close>
  using assms
proof (induction seq)
  case (Bcomp seq1 seq2)
  hence "\<Gamma> \<Turnstile> [\<lambda>tw. eval Q [tw] ns ss] seq1 [\<lambda>tw. eval Q [tw] ns ss]"
    and "\<Gamma> \<Turnstile> [\<lambda>tw. eval Q [tw] ns ss] seq2 [\<lambda>tw. eval Q [tw] ns ss]"
    by auto
  hence "\<Gamma> \<Turnstile> [\<lambda>tw. eval Q [tw] ns ss] (Bcomp seq1 seq2) [\<lambda>tw. eval Q [tw] ns ss]"
    unfolding seq_hoare_valid2_wt_def using Bcomp(4) world_seq_exec_comp
    by (smt Bcomp.prems(3) nonneg_delay.simps(2) seq_hoare_valid2_def
    seq_stmt_preserve_wityping_hoare seq_wt_cases(2) soundness_hoare2 world_seq_exec_alt_cases(2)
    world_seq_exec_alt_imp_world_seq_exec world_seq_exec_imp_world_seq_exec_alt)
  then show ?case
    by auto
next
  case (Bguarded x1 seq1 seq2)
  hence *: "\<Gamma> \<Turnstile> [\<lambda>tw. eval Q [tw] ns ss] seq1 [\<lambda>tw. eval Q [tw] ns ss]"
    and ** : "\<Gamma> \<Turnstile> [\<lambda>tw. eval Q [tw] ns ss] seq2 [\<lambda>tw. eval Q [tw] ns ss]"
    by auto
  have "nonneg_delay seq1" and "nonneg_delay seq2"
    using Bguarded by auto
  have "\<Gamma> \<Turnstile> [\<lambda>a. eval Q [a] ns ss \<and> eval_world_raw2 a x1 = Bv True] seq1 [\<lambda>tw . eval Q [tw] ns ss]" and 
      " \<Gamma> \<Turnstile> [\<lambda>a. eval Q [a] ns ss \<and> eval_world_raw2 a x1 = Bv False] seq2 [\<lambda>tw . eval Q [tw] ns ss]"
    using * ** by (smt seq_hoare_valid2_wt_def)+
  then show ?case 
    unfolding seq_hoare_valid2_wt_def world_seq_exec_alt_def[OF Bguarded(4), THEN sym]
    world_seq_exec_alt_def[OF `nonneg_delay seq1`, THEN sym] world_seq_exec_alt_def[OF `nonneg_delay seq2`, THEN sym]
    by (smt "*" "**" Bguarded.prems(2) \<open>\<And>tw. world_seq_exec tw seq1 = world_seq_exec_alt tw seq1\<close>
    \<open>\<And>tw. world_seq_exec tw seq2 = world_seq_exec_alt tw seq2\<close> interp_assertion.simps
    interp_hoare_seq.simps seq_hoare_valid2_wt_def world_seq_exec_alt_cases(3)
    world_seq_exec_imp_world_seq_exec_alt)
next
  case (Bassign_trans x1 x2 x3)
  hence "x1 \<notin> set ss"
    by auto
  have \<open>\<Gamma> \<turnstile> [wp3_fun \<Gamma> (Bassign_trans x1 x2 x3) (\<lambda>tw. eval Q [tw] ns ss)] Bassign_trans x1 x2 x3 [\<lambda>tw. eval Q [tw] ns ss]\<close>
    using wp3_fun_is_pre Bassign_trans  by metis
  hence *: \<open>\<Gamma> \<Turnstile> [wp3_fun \<Gamma> (Bassign_trans x1 x2 x3) (\<lambda>tw. eval Q [tw] ns ss)] Bassign_trans x1 x2 x3 [\<lambda>tw. eval Q [tw] ns ss]\<close>
    using Bassign_trans  by (simp add: seq_hoare3_soundness) 
  have "\<And>tw. eval Q [tw[x1, x3 :=\<^sub>2 eval_world_raw2 tw x2]] ns ss = eval Q [tw] ns ss"
    using eval_free_vars[OF `x1 \<notin> set ss` Bassign_trans(4)]
    by (metis One_nat_def add.commute assms(5) list.size(3) plus_1_eq_Suc)
  hence "wp3_fun \<Gamma> (Bassign_trans x1 x2 x3) (\<lambda>tw. eval Q [tw] ns ss) = (\<lambda>tw. wityping \<Gamma> (snd tw) \<and> eval Q [tw] ns ss)"
    by auto
  hence \<open>\<Gamma> \<Turnstile> [\<lambda>tw. wityping \<Gamma> (snd tw) \<and> eval Q [tw] ns ss] Bassign_trans x1 x2 x3 [\<lambda>tw. eval Q [tw] ns ss]\<close>
    using * by auto
  then show ?case 
    by (simp add: seq_hoare_valid2_wt_def)
next             
  case (Bassign_inert x1 x2 x3)
  hence "x1 \<notin> set ss"
    by auto
  have \<open>\<Gamma> \<turnstile> [wp3_fun \<Gamma> (Bassign_inert x1 x2 x3) (\<lambda>tw. eval Q [tw] ns ss)] Bassign_inert x1 x2 x3 [\<lambda>tw. eval Q [tw] ns ss]\<close>
    using wp3_fun_is_pre Bassign_inert  by metis
  hence *: \<open>\<Gamma> \<Turnstile> [wp3_fun \<Gamma> (Bassign_inert x1 x2 x3) (\<lambda>tw. eval Q [tw] ns ss)] Bassign_inert x1 x2 x3 [\<lambda>tw. eval Q [tw] ns ss]\<close>
    using Bassign_inert  by (simp add: seq_hoare3_soundness)
  have "\<And>tw. eval Q [tw\<lbrakk>x1, x3 :=\<^sub>2 eval_world_raw2 tw x2\<rbrakk>] ns ss = eval Q [tw] ns ss"
    using eval_free_vars_inert[OF `x1 \<notin> set ss` Bassign_inert(4)]  
    by (metis (full_types) One_nat_def Suc_eq_plus1 assms(5) list.size(3))
  hence "wp3_fun \<Gamma> (Bassign_inert x1 x2 x3) (\<lambda>tw. eval Q [tw] ns ss) = (\<lambda>tw. wityping \<Gamma> (snd tw) \<and> eval Q [tw] ns ss)"
    by auto
  hence \<open>\<Gamma> \<Turnstile> [\<lambda>tw. wityping \<Gamma> (snd tw) \<and> eval Q [tw] ns ss] Bassign_inert x1 x2 x3 [\<lambda>tw. eval Q [tw] ns ss]\<close>
    using * by auto
  then show ?case 
    by (simp add: seq_hoare_valid2_wt_def)
next
  case Bnull
  then show ?case 
    by (simp add: Null3 seq_hoare3_soundness)
next
  case (Bcase exp choices)
  hence "\<Gamma> \<Turnstile> [\<lambda>tw. eval Q [tw] ns ss] Bcase exp choices [\<lambda>tw. eval Q [tw] ns ss]"
  proof (induction choices)
    case Nil
    have "wp3_fun \<Gamma> (Bcase exp []) (\<lambda>tw. eval Q [tw] ns ss) = (\<lambda>tw. eval Q [tw] ns ss \<and> wityping \<Gamma> (snd tw))"
      unfolding wp3_fun.simps by auto
    have \<open>\<Gamma> \<turnstile> [wp3_fun \<Gamma> (Bcase exp []) (\<lambda>tw. eval Q [tw] ns ss)] Bcase exp [] [\<lambda>tw. eval Q [tw] ns ss]\<close>
      using wp3_fun_is_pre Nil  by metis
    hence *: \<open>\<Gamma> \<Turnstile> [wp3_fun \<Gamma> (Bcase exp []) (\<lambda>tw. eval Q [tw] ns ss)] Bcase exp [] [\<lambda>tw. eval Q [tw] ns ss]\<close>
      using Nil by (simp add: seq_hoare3_soundness)
    hence \<open>\<Gamma> \<Turnstile> [\<lambda>tw. wityping \<Gamma> (snd tw) \<and> eval Q [tw] ns ss] Bcase exp [] [\<lambda>tw. eval Q [tw] ns ss]\<close>
      by (smt \<open>wp3_fun \<Gamma> (Bcase exp []) (\<lambda>tw. eval Q [tw] ns ss) = (\<lambda>tw. eval Q [tw] ns ss \<and> wityping \<Gamma> (snd tw))\<close> seq_hoare_valid2_wt_def)
    thus ?case
      using Nil Bcase_empty_choices3 interp_hoare_seq.simps seq_hoare3_soundness by blast
  next
    case (Cons a choices)
    obtain seq exp' where "a = (Others, seq) \<or> a = (Explicit exp', seq)"
      by (metis choices.exhaust_sel prod.collapse)
    moreover
    { assume "a = (Others, seq)"
      hence "(Others, seq) \<in> set (a # choices)" and "seq \<in> Basic_BNFs.snds (Others, seq)"
        by auto
      moreover have "signals_of seq \<inter> set ss = {}" and "nonneg_delay seq"
        using Cons(3-4) unfolding `a = (Others, seq)` by auto
      moreover have "seq_wt \<Gamma> seq"
        using Cons(5) seq_wt.cases unfolding `a = (Others, seq)` by blast
      ultimately have "interp_hoare_seq (Hoare (Abs Q) (Abs Q)) ns ss ns ss \<Gamma> seq"
        using Cons(2) Cons(6) assms(5) by blast
      hence " \<Gamma> \<Turnstile> [\<lambda>tw. eval Q [tw] ns ss] seq [\<lambda>tw. eval Q [tw] ns ss] "
        by auto
      hence "\<Gamma> \<Turnstile> [\<lambda>tw. eval Q [tw] ns ss] Bcase exp (a # choices) [\<lambda>tw. eval Q [tw] ns ss]"
        unfolding `a = (Others, seq)`  by (smt bcase_others_tw_elim seq_hoare_valid2_wt_def)  
      hence ?case    
        by auto }
    moreover
    { assume "a = (Explicit exp', seq) "
      moreover hence "seq \<in> Basic_BNFs.snds (Explicit exp', seq)"
        by auto
      moreover have "signals_of seq \<inter> set ss = {}"
        using Cons(3) unfolding `a = (Explicit exp', seq)` by auto
      moreover have "nonneg_delay seq"
        using Cons(4) unfolding `a = (Explicit exp', seq)` by auto
      moreover have "seq_wt \<Gamma> seq"
        using Bcase(4) unfolding `a = (Explicit exp', seq)` using seq_wt_cases_bcase
        using Cons.prems(4) calculation(1) by blast
      ultimately have "interp_hoare_seq (Hoare (Abs Q) (Abs Q)) ns ss ns ss \<Gamma> seq"
        using Cons(2) Cons(6)   by (meson assms(5) list.set_intros(1))
      hence " \<Gamma> \<Turnstile> [\<lambda>tw. eval Q [tw] ns ss] seq [\<lambda>tw. eval Q [tw] ns ss] "
        by auto
      have a : "signals_of (Bcase exp choices) \<inter> set ss = {}" and b: "nonneg_delay (Bcase exp choices)"
        using Cons(3-4) by auto
      have c : "seq_wt \<Gamma> (Bcase exp choices)"
        using  seq_wt_cases_bcase[OF Cons(5)]
        by (smt \<open>a = (Explicit exp', seq)\<close> choices.simps(3) fstI list.distinct(1) list.inject)
      have d : " \<And>x2a x2aa.
      x2a \<in> set choices \<Longrightarrow>
      x2aa \<in> Basic_BNFs.snds x2a \<Longrightarrow>
      signals_of x2aa \<inter> set ss = {} \<Longrightarrow> nonneg_delay x2aa \<Longrightarrow> seq_wt \<Gamma> x2aa \<Longrightarrow> wf_form_sig Q (length ss) 0 \<Longrightarrow> interp_hoare_seq (Hoare (Abs Q) (Abs Q))  ns ss ns ss \<Gamma> x2aa"
        using Cons(2) assms(5) by auto
      have "\<Gamma> \<Turnstile> [\<lambda>tw. eval Q [tw] ns ss] Bcase exp choices [\<lambda>tw. eval Q [tw] ns ss]"
        using Cons(1)[OF d a b c `wf_form_sig Q (length ss) 0`]  using Cons.IH a b c d assms(5) by blast
      hence ?case
        unfolding `a = (Explicit exp', seq)`
        using \<open>\<Gamma> \<Turnstile> [\<lambda>tw. eval Q [tw] ns ss] seq [\<lambda>tw. eval Q [tw] ns ss]\<close>
        Bcase_if3 seq_hoare3_soundness 
        by (smt Cons.prems(3) \<open>a = (Explicit exp', seq)\<close> \<open>nonneg_delay seq\<close> b
        seq_hoare_valid2_wt_def world_seq_exec_alt_cases(6) world_seq_exec_alt_imp_world_seq_exec
        world_seq_exec_imp_world_seq_exec_alt) }
    ultimately show ?case 
      by auto
  qed
 then show ?case 
    by auto
qed

lemma interp_hoare_conc_free_vars:
  assumes \<open>set (signals_from cs) \<inter> set ss = {}\<close>
  assumes \<open>conc_stmt_wf cs\<close> and \<open>nonneg_delay_conc cs\<close> and \<open> conc_wt \<Gamma> cs\<close>
  assumes \<open>wf_form_sig Q (length ss) 0\<close>
  assumes \<open>highest_idx_form_rwline Q \<le> 1\<close>
  shows \<open>interp_hoare_conc (Hoare (Abs Q) (Abs Q)) ns ss ns ss \<Gamma> cs\<close>
  using assms 
proof (induction cs)
  case (Bpar cs1 cs2)
  hence "conc_stmt_wf cs1 " and "conc_stmt_wf cs2" and "set (signals_from cs1) \<inter> set ss = {}"
    and "set (signals_from cs2) \<inter> set ss = {}"
    by auto
  hence "interp_hoare_conc (Hoare (Abs Q) (Abs Q)) ns ss ns ss \<Gamma> cs1" and 
        \<open>interp_hoare_conc (Hoare (Abs Q) (Abs Q)) ns ss ns ss \<Gamma> cs2\<close>
    using Bpar by auto
  hence "\<Gamma> \<Turnstile> \<lbrace>\<lambda>tw. eval Q [tw] ns ss\<rbrace> cs1 \<lbrace>\<lambda>tw. eval Q [tw] ns ss\<rbrace>" and 
        \<open>\<Gamma> \<Turnstile> \<lbrace>\<lambda>tw. eval Q [tw] ns ss\<rbrace> cs2 \<lbrace>\<lambda>tw. eval Q [tw] ns ss\<rbrace>\<close>
    by auto
  hence "\<Gamma> \<Turnstile> \<lbrace>\<lambda>tw. eval Q [tw] ns ss\<rbrace> cs1 || cs2 \<lbrace>\<lambda>tw. eval Q [tw] ns ss\<rbrace>"
    using parallel_valid[OF _ _ Bpar(4-6)] by auto
  then show ?case    
    by auto
next
  case (Bsingle x1 x2)
  hence 0: "set (signals_in x2) \<inter> set ss = {}" and 1: "nonneg_delay x2" and 2: "seq_wt \<Gamma> x2"
    by auto
  have "\<Gamma> \<Turnstile> [\<lambda>tw. eval Q [tw] ns ss] x2 [\<lambda>tw. eval Q [tw] ns ss]"
    using interp_hoare_seq_free_vars[OF 0 1 2 Bsingle(5)]  using assms(6) by auto
  moreover have "\<forall>tw. eval Q [tw] ns ss \<and> disjnt x1 (event_of tw) \<longrightarrow> eval Q [tw] ns ss"
    by auto
  moreover have "\<And>P Q. \<Gamma> \<Turnstile> [\<lambda>tw. P tw \<and> \<not> disjnt x1 (event_of tw)] x2 [Q] \<Longrightarrow> \<forall>tw. P tw \<and> disjnt x1 (event_of tw) \<longrightarrow> Q tw \<Longrightarrow> \<Gamma> \<Turnstile> \<lbrace>P\<rbrace>  process x1 : x2 \<lbrace>Q\<rbrace>"
  proof -
    fix P Q
    have 0: "\<Gamma> \<turnstile> [\<lambda>tw. P tw \<and> \<not> disjnt x1 (event_of tw)] x2 [Q] \<Longrightarrow> \<forall>tw. P tw \<and> disjnt x1 (event_of tw) \<longrightarrow> Q tw \<Longrightarrow> \<Gamma> \<turnstile> \<lbrace>P\<rbrace>  process x1 : x2 \<lbrace>Q\<rbrace>"
      using Single[where sl="x1" and ss="x2"] by auto
    moreover have  1: "\<Gamma> \<turnstile> [\<lambda>tw. P tw \<and> \<not> disjnt x1 (event_of tw)] x2 [Q] \<Longrightarrow> \<Gamma> \<Turnstile> [\<lambda>tw. P tw \<and> \<not> disjnt x1 (event_of tw)] x2 [Q]"
      using seq_hoare3_soundness[OF _ 2 1] by blast
    moreover have 2: "\<Gamma> \<turnstile> \<lbrace>P\<rbrace>  process x1 : x2 \<lbrace>Q\<rbrace> \<Longrightarrow> \<Gamma> \<Turnstile> \<lbrace>P\<rbrace>  process x1 : x2 \<lbrace>Q\<rbrace>"
      using soundness_conc_hoare[OF _ `conc_wt \<Gamma> (process x1 : x2)` `conc_stmt_wf ( process x1 : x2)` `nonneg_delay_conc ( process x1 : x2)`] by auto
    ultimately show " \<Gamma> \<Turnstile> [\<lambda>tw. P tw \<and> \<not> disjnt x1 (event_of tw)] x2 [Q] \<Longrightarrow> \<forall>tw. P tw \<and> disjnt x1 (event_of tw) \<longrightarrow> Q tw \<Longrightarrow> \<Gamma> \<Turnstile> \<lbrace>P\<rbrace>  process x1 : x2 \<lbrace>Q\<rbrace>"
      by (auto simp add: `seq_wt \<Gamma> x2` `nonneg_delay x2` seq_hoare_wt_complete)
  qed
  ultimately have "\<Gamma> \<Turnstile> \<lbrace>\<lambda>tw. eval Q [tw] ns ss\<rbrace> process x1 : x2 \<lbrace>\<lambda>tw. eval Q [tw] ns ss\<rbrace>"
    by (smt seq_hoare_valid2_wt_def)
  then show ?case 
    by auto
qed

lemma conc_hoare_and_post:
  assumes \<open>\<Gamma> \<Turnstile> \<lbrace>P\<rbrace> cs \<lbrace>Q1\<rbrace>\<close> and \<open>\<Gamma> \<Turnstile> \<lbrace>P\<rbrace> cs \<lbrace>Q2\<rbrace>\<close>
  shows   \<open>\<Gamma> \<Turnstile> \<lbrace>P\<rbrace> cs \<lbrace>\<lambda>tw. Q1 tw \<and> Q2 tw\<rbrace>\<close>
  by (smt assms(1) assms(2) conc_hoare_valid_wt_def)

lemma interp_hoare_conc_and:
  assumes \<open>interp_hoare_conc (Hoare (Abs prea) (Abs posta)) ns1 ss1 ns2 ss2 \<Gamma> cs\<close>
  assumes \<open>set (signals_from cs) \<inter> set ss' = {}\<close>
  assumes \<open>conc_stmt_wf cs\<close> and \<open>nonneg_delay_conc cs\<close> and \<open> conc_wt \<Gamma> cs\<close>
  assumes \<open>wf_form_sig Q (length ss') 0\<close>
  assumes \<open>wf_assertion (Abs prea) (length ns1) (length ss1)\<close> 
  assumes \<open>wf_assertion (Abs posta) (length ns2) (length ss2)\<close>
  assumes \<open>highest_idx_form_rwline Q \<le> 1\<close>
  shows   \<open>interp_hoare_conc (Hoare (Abs (Rsepand prea Q)) (Abs (Rsepand posta Q))) (ns1 @ ns') (ss1 @ ss') (ns2 @ ns') (ss2 @ ss') \<Gamma> cs\<close>
proof -
  have "\<Gamma> \<Turnstile> \<lbrace>interp_assertion (Abs prea) ns1 ss1\<rbrace> cs \<lbrace>interp_assertion (Abs posta) ns2 ss2\<rbrace>"
    using assms by auto
  hence "\<Gamma> \<Turnstile> \<lbrace>\<lambda>tw. eval prea [tw] ns1 ss1\<rbrace> cs \<lbrace>\<lambda>tw. eval posta [tw] ns2 ss2\<rbrace>"
    by auto
  hence "\<And>Q. \<Gamma> \<Turnstile> \<lbrace>\<lambda>tw. eval prea [tw] ns1 ss1 \<and> Q tw\<rbrace> cs \<lbrace>\<lambda>tw. eval posta [tw] ns2 ss2\<rbrace>"
    by (smt conc_hoare_valid_wt_def)
  hence *: "\<Gamma> \<Turnstile> \<lbrace>\<lambda>tw. eval prea [tw] ns1 ss1 \<and> eval Q [tw] ns' ss'\<rbrace> cs \<lbrace>\<lambda>tw. eval posta [tw] ns2 ss2\<rbrace>"
    by auto
  have "\<Gamma> \<Turnstile> \<lbrace>\<lambda>tw. eval Q [tw] ns' ss'\<rbrace> cs \<lbrace>\<lambda>tw. eval Q [tw] ns' ss'\<rbrace>"
    using interp_hoare_conc_free_vars[OF  assms(2-6)] assms(9) by auto
  hence **: "\<Gamma> \<Turnstile> \<lbrace>\<lambda>tw. eval prea [tw] ns1 ss1 \<and> eval Q [tw] ns' ss'\<rbrace> cs \<lbrace>\<lambda>tw. eval Q [tw] ns' ss'\<rbrace>"
    by (smt conc_hoare_valid_wt_def)
  have "\<Gamma> \<Turnstile> \<lbrace>\<lambda>tw. eval prea [tw] ns1 ss1 \<and> eval Q [tw] ns' ss'\<rbrace> cs \<lbrace>\<lambda>tw. eval posta [tw] ns2 ss2 \<and> eval Q [tw] ns' ss'\<rbrace>"
    by (auto intro!: conc_hoare_and_post simp add: * **)
  moreover have "highest_idx_form_rwline prea \<le> 1" and "highest_idx_form_nat prea = length ns1" and "highest_idx_form_sig prea = length ss1"
                "highest_idx_form_rwline posta \<le> 1" and "highest_idx_form_nat posta = length ns2" and "highest_idx_form_sig posta = length ss2"
    using assms(7-8) by auto
  ultimately have "\<Gamma> \<Turnstile> \<lbrace>\<lambda>tw. eval (Rsepand prea Q) [tw] (ns1 @ ns') (ss1 @ ss')\<rbrace> cs \<lbrace>\<lambda>tw. eval (Rsepand posta Q) [tw] (ns2 @ ns') (ss2 @ ss')\<rbrace>"
    by auto
  thus ?thesis
    by auto
qed

lemma interp_hoare_conc_parallel:
  assumes \<open>interp_hoare_conc (Hoare (Abs prea) (Abs posta)) nsa1 ssa1 nsa2 ssa2 \<Gamma> cs1\<close>
  assumes \<open>interp_hoare_conc (Hoare (Abs preb) (Abs postb)) nsb1 ssb1 nsb2 ssb2 \<Gamma> cs2\<close>
  assumes \<open>set (ssa2) \<inter> set (signals_from cs2) = {}\<close> and \<open>set (ssb1) \<inter> set (signals_from cs1) = {}\<close>
  assumes \<open>conc_stmt_wf (cs1 || cs2)\<close> and \<open>nonneg_delay_conc (cs1 || cs2)\<close> and \<open>conc_wt \<Gamma> (cs1 || cs2)\<close>
  assumes \<open>wf_form_sig preb (length ssb1) 0\<close>
  assumes \<open>wf_assertion (Abs prea) (length nsa1) (length ssa1)\<close> 
  assumes \<open>wf_assertion (Abs posta) (length nsa2) (length ssa2)\<close>
  assumes \<open>wf_form_sig posta (length ssa2) 0\<close>
  assumes \<open>wf_assertion (Abs preb) (length nsb1) (length ssb1)\<close>
  assumes \<open>wf_assertion (Abs postb) (length nsb2) (length ssb2)\<close>
  shows   \<open>interp_hoare_conc (Hoare (Abs (Rsepand prea preb)) (Abs (Rsepand posta postb))) (nsa1 @ nsb1) (ssa1 @ ssb1) 
                                                                                           (nsa2 @ nsb2) (ssa2 @ ssb2) \<Gamma> (cs1 || cs2)\<close>
proof -
  have "\<Gamma> \<Turnstile> \<lbrace>\<lambda>tw. eval prea [tw] nsa1 ssa1\<rbrace> cs1 \<lbrace>\<lambda>tw. eval posta [tw] nsa2 ssa2\<rbrace>" and 
       "\<Gamma> \<Turnstile> \<lbrace>\<lambda>tw. eval preb [tw] nsb1 ssb1\<rbrace> cs2 \<lbrace>\<lambda>tw. eval postb [tw] nsb2 ssb2\<rbrace>"
    using assms(1-2) by auto
  have "set (signals_from cs1) \<inter> set ssb1 = {}"
    using assms(4) by auto
  have "conc_stmt_wf cs1" and "nonneg_delay_conc (cs1)" and "conc_wt \<Gamma> (cs1)"
    using assms(5-7) by auto
  have \<open>interp_hoare_conc (Hoare (Abs (Rsepand prea preb)) (Abs (Rsepand posta preb))) (nsa1 @ nsb1) (ssa1 @ ssb1) (nsa2 @ nsb1) (ssa2 @ ssb1) \<Gamma> cs1\<close>
    using interp_hoare_conc_and[OF assms(1) `set (signals_from cs1) \<inter> set ssb1 = {}` `conc_stmt_wf cs1` `nonneg_delay_conc (cs1)` `conc_wt \<Gamma> (cs1)` assms(8-10)]
    using assms(12) wf_assertion.simps by blast
  hence *: "\<Gamma> \<Turnstile> \<lbrace>\<lambda>tw. eval prea [tw] nsa1 ssa1 \<and> eval preb [tw] nsb1 ssb1\<rbrace> cs1 \<lbrace>\<lambda>tw. eval posta [tw] nsa2 ssa2 \<and> eval preb [tw] nsb1 ssb1\<rbrace>"
    using assms(9-10) by auto
  have " set (signals_from cs2) \<inter> set ssa2 = {}"
    using assms(3) by auto
  have "conc_stmt_wf cs2" and "nonneg_delay_conc (cs2)" and "conc_wt \<Gamma> (cs2)"
    using assms(5-7) by auto
  have \<open>interp_hoare_conc (Hoare (Abs (Rsepand preb posta)) (Abs (Rsepand postb posta))) (nsb1 @ nsa2) (ssb1 @ ssa2) (nsb2 @ nsa2) (ssb2 @ ssa2) \<Gamma> cs2\<close>
    using interp_hoare_conc_and[OF assms(2) `set (signals_from cs2) \<inter> set ssa2 = {}` `conc_stmt_wf cs2` `nonneg_delay_conc (cs2)` `conc_wt \<Gamma> (cs2)`
                                   assms(11-13)] 
    using assms(10) wf_assertion.simps by blast
  hence "\<Gamma> \<Turnstile> \<lbrace>\<lambda>tw. eval preb [tw] nsb1 ssb1 \<and> eval posta [tw] nsa2 ssa2\<rbrace> cs2 \<lbrace>\<lambda>tw. eval postb [tw] nsb2 ssb2 \<and> eval posta [tw] nsa2 ssa2\<rbrace>"
    using assms(12-13) by auto
  hence "\<Gamma> \<Turnstile> \<lbrace>\<lambda>tw. eval posta [tw] nsa2 ssa2 \<and> eval preb [tw] nsb1 ssb1\<rbrace> cs2 \<lbrace>\<lambda>tw. eval posta [tw] nsa2 ssa2 \<and> eval postb [tw] nsb2 ssb2\<rbrace>"
    unfolding conc_hoare_valid_wt_def by meson
  hence "\<Gamma> \<Turnstile> \<lbrace>\<lambda>tw. eval prea [tw] nsa1 ssa1 \<and> eval preb [tw] nsb1 ssb1\<rbrace> (cs1 || cs2) \<lbrace>\<lambda>tw. eval posta [tw] nsa2 ssa2 \<and> eval postb [tw] nsb2 ssb2\<rbrace>"
    using parallel_valid  by (metis (no_types, lifting) "*" assms(5) assms(6) assms(7))
  thus ?thesis
    using assms(11-13) assms(9-10) by auto
qed

primrec inter_hoare_triple :: \<open>hoare_triple \<Rightarrow>  nat list \<Rightarrow> 'a sig list \<Rightarrow> 
                                                nat list \<Rightarrow> 'a sig list \<Rightarrow> 'a sig tyenv \<Rightarrow> 'a sig conc_stmt \<Rightarrow> bool\<close> where
  \<open>inter_hoare_triple (Hoare pre post) ns1 ss1 ns2 ss2 \<Gamma> cs = (\<Gamma> \<Turnstile>\<^sub>s \<lbrace>interp_assertion pre ns1 ss1\<rbrace> cs \<lbrace>interp_assertion post ns2 ss2\<rbrace>)\<close>

experiment begin

abbreviation "S_INIT \<equiv> Bliteral Neu [False, False, False]"

abbreviation "V_INIT \<equiv> Lv Neu [False, False, False]" 
abbreviation "V_WAIT \<equiv> Lv Neu [False, False, True ]"
abbreviation "V_PRE  \<equiv> Lv Neu [False, True , False]"
abbreviation "V_PROC \<equiv> Lv Neu [False, True , True ]"
abbreviation "V_POST \<equiv> Lv Neu [True , False, False]" 

abbreviation "U_ZERO3  \<equiv>  [False, False, False]"
abbreviation "U_ZERO32 \<equiv>  replicate 32 False"

abbreviation "V_ZERO3   \<equiv> Lv Uns U_ZERO3"
abbreviation "V_ZERO32  \<equiv> Lv signedness.Sig U_ZERO32"

datatype test = INPUT | OUTPUT | INREADY | OUTREADY | OUTREADY_REG 
  | NEXT_OUTREADYREG | ACCUM | NEXT_ACCUM  | COUNTER | NEXT_COUNTER | FRAC | NEXT_FRAC 
  | COMMON | NEXT_COMMON  | CTR_NEQ_0 | CLK | RST | STATE | NEXT_STATE | SQUARE_TEMP 
  | CTR_MSB  | CTR_LSB  | TERM1

definition "registers \<equiv> (process {Sname CLK} : 
              Bguarded (Band (Bsig (Sname CLK)) (Bsig_event (Sname CLK))) 
                (Bguarded (Bsig (Sname RST)) 
                    (Bcomp (Bassign_trans (Sname ACCUM) (Bliteral signedness.Sig U_ZERO32) 1)      
                    (Bcomp (Bassign_trans (Sname COUNTER) (Bliteral Uns U_ZERO3 ) 1)      
                    (Bcomp (Bassign_trans (Sname FRAC) (Bliteral signedness.Sig U_ZERO32) 1) 
                    (Bcomp (Bassign_trans (Sname COMMON) (Bliteral signedness.Sig U_ZERO32) 1) 
                    (Bcomp (Bassign_trans (Sname STATE) (S_INIT)                1)
                           (Bassign_trans (Sname OUTREADY_REG) (Bfalse)                1))))))

                    (Bcomp (Bassign_trans (Sname ACCUM) (Bsig (Sname NEXT_ACCUM))       1)     
                    (Bcomp (Bassign_trans (Sname COUNTER) (Bsig (Sname NEXT_COUNTER))     1)     
                    (Bcomp (Bassign_trans (Sname FRAC) (Bsig (Sname NEXT_FRAC))        1) 
                    (Bcomp (Bassign_trans (Sname COMMON) (Bsig (Sname NEXT_COMMON))      1) 
                    (Bcomp (Bassign_trans (Sname STATE) (Bsig (Sname NEXT_STATE))       1)
                           (Bassign_trans (Sname OUTREADY_REG) (Bsig (Sname NEXT_OUTREADYREG)) 1))))))) 
                (Bnull))"

lemma interp_true:
  \<open>interp_assertion (Abs (RAnd RT RT)) [] [] = (\<lambda>tw :: nat \<times> test sig worldline_init. True)\<close>
  by simp

lemma
  \<open>inter_hoare_triple (Hoare (Abs (RAnd RT RT)) (Abs (RAnd RT RT))) [] [] [] [] \<Gamma> registers = undefined\<close>
  apply simp
  oops

(* proposition
  \<open>\<Gamma> \<Turnstile>\<^sub>s \<lbrace>\<lambda>tw. True\<rbrace> registers \<lbrace>\<lambda>tw. True\<rbrace>\<close>
  unfolding interp_true[symmetric]
  apply (reify inter_hoare_triple.simps)
  oops
 *)

definition Inv :: \<open>test sig assn2\<close> where 
  "Inv tw \<equiv> disjnt {Sname CLK} (event_of tw) \<or> wline_of tw (Sname CLK) (fst tw) \<noteq> (Bv True) \<longrightarrow> 
      (\<forall>n :: nat. fst tw < n \<longrightarrow> (\<forall>s :: test sig. s \<in> {Sname ACCUM, Sname COUNTER, Sname FRAC, Sname COMMON, Sname STATE, Sname OUTREADY_REG} \<longrightarrow> wline_of tw s n = wline_of tw s (fst tw)))"

schematic_goal
  "eval ?x ?y ?z (?a :: test sig list) = (disjnt {Sname CLK} (event_of tw) \<or> wline_of tw (Sname CLK) (fst tw) \<noteq> (Bv True) \<longrightarrow> 
      (\<forall>n :: nat. fst tw < n \<longrightarrow> (\<forall>s :: test sig. s \<in> {Sname ACCUM, Sname COUNTER, Sname FRAC, Sname COMMON, Sname STATE, Sname OUTREADY_REG} \<longrightarrow> wline_of tw s n = wline_of tw s (fst tw))))"
  apply (reify eval.simps Irwline.simps Irnat_simps Irsig_simps Irval_simps Irset.simps Irint_simps
         ("disjnt {Sname CLK} (event_of tw) \<or> wline_of tw (Sname CLK) (fst tw) \<noteq> (Bv True) \<longrightarrow> 
      (\<forall>n :: nat. fst tw < n \<longrightarrow> (\<forall>s :: test sig. s \<in> {Sname ACCUM, Sname COUNTER, Sname FRAC, Sname COMMON, Sname STATE, Sname OUTREADY_REG} \<longrightarrow> wline_of tw s n = wline_of tw s (fst tw)))"))
  by rule

schematic_goal
  \<open>highest_idx_form_sig ((RImp (ROr (RDisevt (LCons (Svar (Suc (Suc (Suc (Suc (Suc (Suc 0))))))) LEmpty) (Wvar 0)) (Rnot (RVEq (Vwline (Wvar 0) (Svar (Suc (Suc (Suc (Suc (Suc (Suc 0))))))) (NFst (Wvar 0))) (VC (Bv True)))))
     (RNall
       (RImp (RNLT (NFst (Wvar 0)) (NVar 0))
         (RSigall
             (
               (LCons (Svar (Suc (Suc (Suc (Suc (Suc (Suc 0)))))))
                 (LCons (Svar (Suc (Suc (Suc (Suc (Suc 0)))))) (LCons (Svar (Suc (Suc (Suc (Suc 0))))) (LCons (Svar (Suc (Suc (Suc 0)))) (LCons (Svar (Suc (Suc 0))) (LCons (Svar (Suc 0)) LEmpty))))))
             )
             (RVEq (Vwline (Wvar 0) (Svar 0) (NVar 0)) (Vwline (Wvar 0) (Svar 0) (NFst (Wvar 0))))))))) = ?n\<close>
  by simp
 
lemma interp_assertion0:
  \<open>interp_assertion (Abs (Rsepand (RImp
     (ROr (RDisevt (LCons (Svar (Suc (Suc (Suc (Suc (Suc (Suc 0))))))) LEmpty) (Wvar 0))
       (Rnot (RVEq (Vwline (Wvar 0) (Svar (Suc (Suc (Suc (Suc (Suc (Suc 0))))))) (NFst (Wvar 0))) (VC (Bv True)))))
     (RNall
       (RImp (RNLT (NFst (Wvar 0)) (NVar 0))
         (RSigall
           (LCons (Svar (Suc (Suc (Suc (Suc (Suc (Suc 0)))))))
             (LCons (Svar (Suc (Suc (Suc (Suc (Suc 0))))))
               (LCons (Svar (Suc (Suc (Suc (Suc 0))))) (LCons (Svar (Suc (Suc (Suc 0)))) (LCons (Svar (Suc (Suc 0))) (LCons (Svar (Suc 0)) LEmpty))))))
           (RVEq (Vwline (Wvar 0) (Svar 0) (NVar 0)) (Vwline (Wvar 0) (Svar 0) (NFst (Wvar 0)))))))) RT))  [][Sname OUTREADY_REG, Sname STATE, Sname COMMON, Sname FRAC, Sname COUNTER, Sname ACCUM, Sname CLK] = Inv\<close>
  unfolding Inv_def
  by simp

(* proposition
  \<open>\<Gamma> \<Turnstile>\<^sub>s \<lbrace>Inv\<rbrace> registers \<lbrace>Inv\<rbrace>\<close>
  unfolding interp_assertion0[symmetric]
  apply (reify inter_hoare_triple.simps)
  oops
 *)

end

lemma highest_idx_rnat_rwline_increase_time [simp]:
  "highest_idx_rnat_rwline (increase_time_rnat x) = highest_idx_rnat_rwline x"
  by (induction x) auto

lemma highest_idx_rval_rwline_increase_time [simp]:
  "highest_idx_rval_rwline (increase_time_rval x) = highest_idx_rval_rwline x"
  by (induction x) (auto simp add: highest_idx_rnat_increase_time highest_idx_rnat_rwline_increase_time)

lemma highest_idx_rint_rwline_increase_time [simp]:
  "highest_idx_rint_rwline (increase_time_rint x) = highest_idx_rint_rwline x"
  by (induction x)
     (auto simp add: highest_idx_rval_rwline_increase_time highest_idx_rnat_rwline_increase_time)

lemma highest_idx_form_rwline_increase_time [simp]:
  "highest_idx_form_rwline (increase_time x) = highest_idx_form_rwline x"
  by (induction x)
     (auto simp add: highest_idx_rnat_rwline_increase_time highest_idx_rval_rwline_increase_time highest_idx_rint_rwline_increase_time)

lemma wf_assertion_increase_time:
  assumes  "wf_assertion (Abs inva) n m"
  shows    "wf_assertion (Abs (increase_time inva)) n m"
  using assms
  by (induction inva arbitrary: m n) auto

lemma wf_rval_sig_increase_time:
  assumes " wf_rval_sig x n m"
  shows " wf_rval_sig (increase_time_rval x) n m"
  using assms by (induction x arbitrary: n m) auto

lemma wf_rint_sig_increase_time:
  "wf_rint_sig x n m \<Longrightarrow> wf_rint_sig (increase_time_rint x) n m"
  by (induction x arbitrary: n m) (auto simp add: wf_rval_sig_increase_time)

lemma wf_form_sig_increase_time:
  assumes "wf_form_sig inva n m"
  shows "wf_form_sig (increase_time inva) n m"
  using assms
  by (induction inva arbitrary: m n)
     (auto simp add: wf_rval_sig_increase_time wf_rint_sig_increase_time)

theorem interp_hgoare_sim_parallel:
  assumes \<open>\<Gamma> \<Turnstile>\<^sub>s \<lbrace>\<lambda>tw. eval inva [tw] nsa ssa\<rbrace> cs1 \<lbrace>\<lambda>tw. eval inva [tw] nsa ssa\<rbrace>\<close>
  assumes \<open>\<Gamma> \<Turnstile>\<^sub>s \<lbrace>\<lambda>tw. eval invb [tw] nsb ssb\<rbrace> cs2 \<lbrace>\<lambda>tw. eval invb [tw] nsb ssb\<rbrace>\<close>
  assumes \<open>set (ssa) \<inter> set (signals_from cs2) = {}\<close> and \<open>set (ssb) \<inter> set (signals_from cs1) = {}\<close>
  assumes "nonneg_delay_conc (cs1 || cs2)" and "conc_stmt_wf (cs1 || cs2)" and "conc_wt \<Gamma> (cs1 || cs2)"
  assumes \<open>wf_form_sig invb (length ssb) 0\<close>
  assumes \<open>wf_assertion (Abs inva) (length nsa) (length ssa)\<close> 
  assumes \<open>wf_form_sig inva (length ssa) 0\<close>
  assumes \<open>wf_assertion (Abs invb) (length nsb) (length ssb)\<close> 
  shows   \<open>\<Gamma> \<Turnstile>\<^sub>s \<lbrace>\<lambda>tw. eval (Rsepand inva invb) [tw] (nsa @ nsb) (ssa @ ssb)\<rbrace> cs1 || cs2 \<lbrace>\<lambda>tw. eval (Rsepand inva invb) [tw] (nsa @ nsb) (ssa @ ssb)\<rbrace>\<close>
proof -
  have "nonneg_delay_conc cs1" and "conc_stmt_wf cs1" and "conc_wt \<Gamma> cs1" 
    using assms by auto
  hence "\<Gamma> \<Turnstile> \<lbrace>\<lambda>tw. eval inva [tw] nsa ssa\<rbrace> cs1 \<lbrace>\<lambda>tw. eval inva [(get_time tw + 1, snd tw)] nsa ssa\<rbrace>"
    using simulation_semi_complete[OF assms(1)] by blast
  hence "\<Gamma> \<Turnstile> \<lbrace>\<lambda>tw. eval inva [tw] nsa ssa\<rbrace> cs1 \<lbrace>\<lambda>tw. eval (increase_time inva) [tw] nsa ssa\<rbrace>"
    using eval_increase_time_correct 
    by (smt One_nat_def add.commute assms(9) conc_hoare_valid_wt_def le_numeral_extra(4) list.simps(8) list.simps(9) list.size(3) list.size(4) plus_1_eq_Suc wf_assertion.simps)
  hence 0: "interp_hoare_conc (Hoare (Abs inva) (Abs (increase_time inva))) nsa ssa nsa ssa \<Gamma> cs1"
    by auto
  have "nonneg_delay_conc cs2" and "conc_stmt_wf cs2" and "conc_wt \<Gamma> cs2" 
    using assms by auto
  hence    "\<Gamma> \<Turnstile> \<lbrace>\<lambda>tw. eval invb [tw] nsb ssb\<rbrace> cs2 \<lbrace>\<lambda>tw. eval invb [(get_time tw + 1, snd tw)] nsb ssb\<rbrace>"
    using simulation_semi_complete[OF assms(2)] by blast
  hence "\<Gamma> \<Turnstile> \<lbrace>\<lambda>tw. eval invb [tw] nsb ssb\<rbrace> cs2 \<lbrace>\<lambda>tw. eval (increase_time invb) [tw] nsb ssb\<rbrace>"
    using eval_increase_time_correct 
    by (smt One_nat_def assms(11) conc_hoare_valid_wt_def le_numeral_extra(4) length_Cons list.simps(8) list.simps(9) list.size(3) wf_assertion.simps)
  hence 1: "interp_hoare_conc (Hoare (Abs invb) (Abs (increase_time invb))) nsb ssb nsb ssb \<Gamma> cs2"
    by auto
  have 2: "wf_assertion (Abs (increase_time inva)) (length nsa) (length ssa)"
    using assms(9) by (auto simp add: wf_assertion_increase_time)
  have 3: "wf_form_sig (increase_time inva) (length ssa) 0"
    using assms(10) by (auto simp add: wf_form_sig_increase_time)
  have 4: "wf_assertion (Abs (increase_time invb)) (length nsb) (length ssb)"
    using assms(11) by (auto simp add: wf_assertion_increase_time)
  have "interp_hoare_conc (Hoare (Abs (Rsepand inva invb)) (Abs (Rsepand (increase_time inva) (increase_time invb)))) (nsa @ nsb) (ssa @ ssb) (nsa @ nsb) (ssa @ ssb) \<Gamma> (cs1 || cs2)"
    using interp_hoare_conc_parallel[OF 0 1 assms(3-4) assms(6) assms(5) assms(7-9) 2 3 assms(11) 4]   
    by auto
  hence "\<Gamma> \<Turnstile> \<lbrace>\<lambda>tw. eval (Rsepand inva invb) [tw] (nsa @ nsb) (ssa @ ssb)\<rbrace> cs1 || cs2 \<lbrace>\<lambda>tw. eval (Rsepand (increase_time inva) (increase_time invb)) [tw] (nsa @ nsb) (ssa @ ssb)\<rbrace>"
    by auto
  hence "\<Gamma> \<Turnstile> \<lbrace>\<lambda>tw. eval (Rsepand inva invb) [tw] (nsa @ nsb) (ssa @ ssb)\<rbrace> cs1 || cs2 \<lbrace>\<lambda>tw. eval (increase_time (Rsepand inva invb)) [tw] (nsa @ nsb) (ssa @ ssb)\<rbrace>"
    by auto
  hence "\<Gamma> \<Turnstile> \<lbrace>\<lambda>tw. eval (Rsepand inva invb) [tw] (nsa @ nsb) (ssa @ ssb)\<rbrace> cs1 || cs2 \<lbrace>\<lambda>tw. eval (Rsepand inva invb) [(fst tw + 1, snd tw)] (nsa @ nsb) (ssa @ ssb)\<rbrace>"
    using eval_increase_time_correct 
    apply simp
    by (smt "2" One_nat_def add.commute assms(11) conc_hoare_valid_wt_def eval_increase_time_correct
    highest_idx_form_rwline_increase_time length_Cons list.simps(8) list.simps(9) list.size(3)
    plus_1_eq_Suc wf_assertion.simps)
  with While_Suc show ?thesis
    by (smt assms(5) assms(6) assms(7) conc_hoare_valid_wt_def sim_hoare_valid_wt_def while_soundness)
qed  
  
lemma wp3_fun_unaffected_wityping:
  assumes "seq_wt \<Gamma> seq"
  shows "wp3_fun \<Gamma> seq (\<lambda>tw. P tw \<and> wityping \<Gamma> (snd tw)) = wp3_fun \<Gamma> seq (\<lambda>tw. P tw)"
  using assms
proof (induction seq)
  case (4 \<Gamma> exp sig dly)
  hence "\<And>tw. wityping \<Gamma> (snd tw) \<Longrightarrow> wityping \<Gamma> (snd tw[ sig, dly :=\<^sub>2 eval_world_raw2 tw exp])"
    unfolding worldline_upd2_def snd_conv  type_of_eval_world_raw2
    by (meson type_of_eval_world_raw2 worldline_upd_preserve_wityping)
  then show ?case 
    by auto
next
  case (5 \<Gamma> exp sig dly)
  hence "\<And>tw. wityping \<Gamma> (snd tw) \<Longrightarrow> wityping \<Gamma> (snd tw\<lbrakk> sig, dly :=\<^sub>2 eval_world_raw2 tw exp\<rbrakk>)"
    unfolding worldline_upd2_def snd_conv type_of_eval_world_raw2
    by (metis sndI type_of_eval_world_raw2 worldline_inert_upd2_def worldline_inert_upd_preserve_wityping)
  then show ?case 
    by auto
qed auto

lemma wp3_conc_unaffected_wityping:
  assumes "conc_wt \<Gamma> cs" and "nonneg_delay_conc cs" and "conc_stmt_wf cs"
  shows   "wp3_conc \<Gamma> cs (\<lambda>tw. P tw \<and> wityping \<Gamma> (snd tw)) = wp3_conc \<Gamma> cs P"
  using assms
proof (induction cs)
  case (1 \<Gamma> ss sl)
  hence *: "conc_wt \<Gamma> ( process sl : ss)"
    using conc_wt.intros(1) by blast
  have " wp3_conc \<Gamma> ( process sl : ss) (\<lambda>tw. P tw \<and> wityping \<Gamma> (snd tw)) = 
       (\<lambda>tw. if disjnt sl (event_of tw) then P tw \<and> wityping \<Gamma> (snd tw) else wp3_fun \<Gamma> ss (\<lambda>tw. P tw \<and> wityping \<Gamma> (snd tw)) tw)"
    unfolding  wp3_conc_single'[OF * 1(2)] by auto
  also have "... = (\<lambda>tw. if disjnt sl (event_of tw) then P tw \<and> wityping \<Gamma> (snd tw) else wp3_fun \<Gamma> ss P tw)"
    unfolding wp3_fun_unaffected_wityping[OF 1(1)] by auto
  finally have "wp3_conc \<Gamma> ( process sl : ss) (\<lambda>tw. P tw \<and> wityping \<Gamma> (snd tw)) = 
        (\<lambda>tw. if disjnt sl (event_of tw) then P tw \<and> wityping \<Gamma> (snd tw) else wp3_fun \<Gamma> ss P tw)"
    by auto
  then show ?case 
    unfolding wp3_conc_single'[OF * 1(2)] by auto    
next
  case (2 \<Gamma> cs1 cs2)
  hence " conc_stmt_wf cs1 " and " conc_stmt_wf cs2 "
    by auto
  hence *: " wp3_conc \<Gamma> cs1 (\<lambda>tw. P tw \<and> wityping \<Gamma> (snd tw)) = wp3_conc \<Gamma> cs1 P" and 
        **: " wp3_conc \<Gamma> cs2 (\<lambda>tw. P tw \<and> wityping \<Gamma> (snd tw)) = wp3_conc \<Gamma> cs2 P"
    using 2 by auto
  have "conc_wt \<Gamma> (cs1 || cs2)"
    using 2  by (simp add: conc_wt.intros(2))
  have "wp3_conc \<Gamma> (cs1 || cs2) (\<lambda>tw. P tw \<and> wityping \<Gamma> (snd tw)) = wp3_conc \<Gamma> cs1 (wp3_conc \<Gamma> cs2 (\<lambda>tw. P tw \<and> wityping \<Gamma> (snd tw)))"
    unfolding wp3_conc_parallel[OF 2(6) 2(5) `conc_wt \<Gamma> (cs1 || cs2)`] by auto
  also have "... = wp3_conc \<Gamma> cs1 (wp3_conc \<Gamma> cs2 P)"
    unfolding ** by auto
  also have "... = wp3_conc \<Gamma> (cs1 || cs2) P"
    using wp3_conc_parallel[OF 2(6) 2(5) `conc_wt \<Gamma> (cs1 || cs2)`] by auto
  finally show ?case
    by auto
qed

lemma wp3_fun_inv:
  assumes "seq_wt \<Gamma> seq"
  assumes \<open>set ss \<inter> set (signals_in seq) = {}\<close>
  assumes \<open>highest_idx_form_rwline Q = 1\<close>
  assumes \<open>wf_form_sig Q (length ss) 0\<close>
  shows "wp3_fun \<Gamma> seq (\<lambda>tw. eval Q [tw] ns ss) = (\<lambda>tw. eval Q [tw] ns ss \<and> wityping \<Gamma> (snd tw))"
  using assms
proof (induction seq arbitrary: Q rule:seq_wt.inducts)
  case (1 \<Gamma>)
  then show ?case by auto
next
  case (2 \<Gamma> s1 s2)
  hence *: "wp3_fun \<Gamma> s2 (\<lambda>tw. eval Q [tw] ns ss) = (\<lambda>tw. eval Q [tw] ns ss \<and> wityping \<Gamma> (snd tw))"
    by auto
  have "set ss \<inter> signals_of (s1) = {}"
    using 2 by auto
  have "wp3_fun \<Gamma> (Bcomp s1 s2) (\<lambda>tw. eval Q [tw] ns ss) = wp3_fun \<Gamma> s1 (wp3_fun \<Gamma> s2 (\<lambda>tw. eval Q [tw] ns ss))"
    by auto
  also have "... = wp3_fun \<Gamma> s1 (\<lambda>tw. eval Q [tw] ns ss \<and> wityping \<Gamma> (snd tw))"
    unfolding * by auto
  also have "... = wp3_fun \<Gamma> s1 (\<lambda>tw. eval Q [tw] ns ss)"
    using wp3_fun_unaffected_wityping[OF `seq_wt \<Gamma> s1`] by auto
  also have "... = (\<lambda>tw. eval Q [tw] ns ss \<and> wityping \<Gamma> (snd tw))"
    using 2(3)[OF `set ss \<inter> signals_of s1 = {}` 2(6) 2(7)] by auto 
  finally show ?case
    by auto
next
  case (3 \<Gamma> g s1 s2)
  hence "wp3_fun \<Gamma> s1 (\<lambda>tw. eval Q [tw] ns ss) = (\<lambda>tw. eval Q [tw] ns ss \<and> wityping \<Gamma> (snd tw))" and 
        "wp3_fun \<Gamma> s2 (\<lambda>tw. eval Q [tw] ns ss) = (\<lambda>tw. eval Q [tw] ns ss \<and> wityping \<Gamma> (snd tw))"
    by auto
  then show ?case 
    by auto
next
  case (4 \<Gamma> exp sig dly)
  hence "sig \<notin> set ss"
    by auto
  have "\<And>a.  eval Q [a[ sig, dly :=\<^sub>2 eval_world_raw2 a exp]] ns ss = eval Q [a] ns ss"
    using eval_free_vars[OF `sig \<notin> set ss` 4(4)] 4(3) by auto  
  then show ?case 
    by auto
next
  case (5 \<Gamma> exp sig dly)
  hence "sig \<notin> set ss"
    by auto
  have "\<And>a.  eval Q [a\<lbrakk> sig, dly :=\<^sub>2 eval_world_raw2 a exp\<rbrakk>] ns ss = eval Q [a] ns ss"
    using eval_free_vars_inert[OF `sig \<notin> set ss` 5(4)] 5(3) by auto  
  then show ?case 
    by auto
next
  case (6 \<Gamma> exp ty)
  then show ?case by auto
next
  case (7 \<Gamma> exp ty ss choices)
  then show ?case by auto
next
  case (8 \<Gamma> exp ty exp' seq choices)
  hence "set ss \<inter> signals_of seq = {}" and "set ss \<inter> signals_of (Bcase exp choices) = {}"
    by auto
  have "wp3_fun \<Gamma> seq (\<lambda>tw. eval Q [tw] ns ss) = (\<lambda>tw. eval Q [tw] ns ss \<and> wityping \<Gamma> (snd tw))"
    using 8(5)[OF `set ss \<inter> signals_of seq = {}` 8(8-9)] by auto
  moreover have " wp3_fun \<Gamma> (Bcase exp choices) (\<lambda>tw. eval Q [tw] ns ss) = (\<lambda>tw. eval Q [tw] ns ss \<and> wityping \<Gamma> (snd tw))"
    using 8(6)[OF `set ss \<inter> signals_of (Bcase exp choices) = {}` 8(8-9)] by auto
  ultimately show ?case 
    by auto
qed

lemma wp3_conc_inv:
  assumes "conc_wt \<Gamma> cs" and "nonneg_delay_conc cs"
  assumes \<open>set ss \<inter> set (signals_from cs) = {}\<close>
  assumes \<open>highest_idx_form_rwline Q = 1\<close>
  assumes \<open>wf_form_sig Q (length ss) 0\<close> and "conc_stmt_wf cs"
  shows "wp3_conc \<Gamma> cs (\<lambda>tw. eval Q [tw] ns ss) = (\<lambda>tw. eval Q [tw] ns ss \<and> wityping \<Gamma> (snd tw))"
  using assms
proof (induction cs arbitrary: Q rule: conc_wt.inducts)
  case (1 \<Gamma> seq sl)  
  hence cwt: " conc_wt \<Gamma> ( process sl : seq)"
    using conc_wt.intros(1) by blast
  have "wp3_conc \<Gamma> ( process sl : seq) (\<lambda>tw. eval Q [tw] ns ss) = (\<lambda>tw. if disjnt sl (event_of tw) then eval Q [tw] ns ss \<and> wityping \<Gamma> (snd tw) else wp3_fun \<Gamma> seq (\<lambda>tw. eval Q [tw] ns ss) tw)"
    unfolding wp3_conc_single'[OF cwt 1(2)] by auto
  also have "... =  (\<lambda>tw. if disjnt sl (event_of tw) then eval Q [tw] ns ss \<and> wityping \<Gamma> (snd tw) else eval Q [tw] ns ss \<and> wityping \<Gamma> (snd tw))"
    unfolding wp3_fun_inv[OF 1(1) 1(3)[unfolded signals_from.simps] 1(4) 1(5)] by auto
  also have "... = (\<lambda>tw. eval Q [tw] ns ss \<and> wityping \<Gamma> (snd tw))"
    by auto
  finally show ?case 
    by auto
next
  case (2 \<Gamma> cs1 cs2)
  hence "nonneg_delay_conc cs1" and "set ss \<inter> set (signals_from cs1) = {} " and "conc_stmt_wf cs1"
    by auto
  hence IH0: "wp3_conc \<Gamma> cs1 (\<lambda>tw. eval Q [tw] ns ss) = (\<lambda>tw. eval Q [tw] ns ss \<and> wityping \<Gamma> (snd tw))"
    using 2(3)[OF _ _ 2(7-8)] by auto
  hence "nonneg_delay_conc cs2" and "set ss \<inter> set (signals_from cs2) = {} " and "conc_stmt_wf cs2"
    using 2 by auto
  hence IH1: "wp3_conc \<Gamma> cs2 (\<lambda>tw. eval Q [tw] ns ss) = (\<lambda>tw. eval Q [tw] ns ss \<and> wityping \<Gamma> (snd tw))"
    using 2(4)[OF _ _ 2(7-8)] by auto
  have *: "conc_wt \<Gamma> (cs1 || cs2)"
    using 2 by (simp add: conc_wt.intros(2))
  have "wp3_conc \<Gamma> (cs1 || cs2) (\<lambda>tw. eval Q [tw] ns ss) = wp3_conc \<Gamma> cs1 (wp3_conc \<Gamma> cs2 (\<lambda>tw. eval Q [tw] ns ss))"
    unfolding wp3_conc_parallel[OF 2(9) 2(5) *] by auto
  also have "... = wp3_conc \<Gamma> cs1 (\<lambda>tw. eval Q [tw] ns ss \<and> wityping \<Gamma> (snd tw))"
    using IH1 by auto
  also have "... = wp3_conc \<Gamma> cs1 (\<lambda>tw. eval Q [tw] ns ss)"
    using wp3_conc_unaffected_wityping
    by (simp add: wp3_conc_unaffected_wityping "2.hyps"(1) \<open>conc_stmt_wf cs1\<close> \<open>nonneg_delay_conc cs1\<close>)
  also have "... = (\<lambda>tw. eval Q [tw] ns ss \<and> wityping \<Gamma> (snd tw))"  
    using IH0 by auto
  finally show ?case 
    by auto
qed
  
lemma wp3_fun_inv2:
  assumes "seq_wt \<Gamma> seq"
  assumes \<open>set ss \<inter> set (signals_in seq) = {}\<close>
  assumes \<open>highest_idx_form_rwline Q = 1\<close>
  assumes \<open>wf_form_sig Q (length ss) 0\<close>
  assumes \<open>sig \<notin> set (signals_in seq)\<close>
  shows "wp3_fun \<Gamma> seq (\<lambda>tw. eval Q [tw[sig, dly :=\<^sub>2 v]] ns ss) = (\<lambda>tw. eval Q [tw[sig, dly :=\<^sub>2 v]] ns ss \<and> wityping \<Gamma> (snd tw))"
  using assms
proof (induction seq arbitrary: Q rule:seq_wt.inducts)
  case (1 \<Gamma>)
  then show ?case by auto
next
  case (2 \<Gamma> s1 s2)
  hence *: "wp3_fun \<Gamma> s2 (\<lambda>tw. eval Q [tw[sig, dly :=\<^sub>2 v]] ns ss) = (\<lambda>tw. eval Q [tw[sig, dly :=\<^sub>2 v]] ns ss \<and> wityping \<Gamma> (snd tw))"
    by auto
  have "set ss \<inter> signals_of (s1) = {}" and "sig \<notin> signals_of s1"
    using 2 by auto
  have "wp3_fun \<Gamma> (Bcomp s1 s2) (\<lambda>tw. eval Q [tw[sig, dly :=\<^sub>2 v]] ns ss) = wp3_fun \<Gamma> s1 (wp3_fun \<Gamma> s2 (\<lambda>tw. eval Q [tw[sig, dly :=\<^sub>2 v]] ns ss))"
    by auto
  also have "... = wp3_fun \<Gamma> s1 (\<lambda>tw. eval Q [tw[sig, dly :=\<^sub>2 v]] ns ss \<and> wityping \<Gamma> (snd tw))"
    unfolding * by auto
  also have "... = wp3_fun \<Gamma> s1 (\<lambda>tw. eval Q [tw[sig, dly :=\<^sub>2 v]] ns ss)"
    using wp3_fun_unaffected_wityping[OF `seq_wt \<Gamma> s1`] by auto
  also have "... = (\<lambda>tw. eval Q [tw[sig, dly :=\<^sub>2 v]] ns ss \<and> wityping \<Gamma> (snd tw))"
    using 2(3)[OF `set ss \<inter> signals_of s1 = {}` 2(6) 2(7) `sig \<notin> signals_of s1`] by auto 
  finally show ?case
    by auto
next
  case (3 \<Gamma> g s1 s2)
  hence "wp3_fun \<Gamma> s1 (\<lambda>tw. eval Q [tw[sig, dly :=\<^sub>2 v]] ns ss) = (\<lambda>tw. eval Q [tw[sig, dly :=\<^sub>2 v]] ns ss \<and> wityping \<Gamma> (snd tw))" and 
        "wp3_fun \<Gamma> s2 (\<lambda>tw. eval Q [tw[sig, dly :=\<^sub>2 v]] ns ss) = (\<lambda>tw. eval Q [tw[sig, dly :=\<^sub>2 v]] ns ss \<and> wityping \<Gamma> (snd tw))"
    by auto
  then show ?case 
    by auto
next
  case (4 \<Gamma> exp sig' dly')
  hence "sig' \<notin> set ss" and "sig' \<noteq> sig"
    by auto
  have "\<And>a.  eval Q [a[ sig', dly' :=\<^sub>2 eval_world_raw2 a exp][ sig, dly :=\<^sub>2 v]] ns ss = eval Q [a[sig, dly :=\<^sub>2 v]] ns ss"
    using eval_free_vars2[OF `sig' \<notin> set ss` 4(4) _ `sig' \<noteq> sig`] 4(3) by auto 
  thus ?case 
    by auto
next
  case (5 \<Gamma> exp sig' dly')
  hence "sig' \<notin> set ss" and "sig' \<noteq> sig"
    by auto
  have *: "\<And>a.  eval Q [a\<lbrakk> sig', dly' :=\<^sub>2 eval_world_raw2 a exp\<rbrakk>[ sig, dly :=\<^sub>2 v]] ns ss = eval Q [a[ sig, dly :=\<^sub>2 v]] ns ss"
    using eval_free_vars_inert2'[OF `sig' \<notin> set ss` 5(4) _ `sig' \<noteq> sig`] 5(3) by auto  
  thus ?case 
    by auto
next
  case (6 \<Gamma> exp ty)
  then show ?case by auto
next
  case (7 \<Gamma> exp ty ss choices)
  then show ?case by auto
next
  case (8 \<Gamma> exp ty exp' seq choices)
  hence "set ss \<inter> signals_of seq = {}" and "set ss \<inter> signals_of (Bcase exp choices) = {}" and "sig \<notin> signals_of seq"
  and "sig \<notin> signals_of (Bcase exp choices)"
    by auto
  have "wp3_fun \<Gamma> seq (\<lambda>tw. eval Q [tw[sig, dly :=\<^sub>2 v]] ns ss) = (\<lambda>tw. eval Q [tw[sig, dly :=\<^sub>2 v]] ns ss \<and> wityping \<Gamma> (snd tw))"
    using 8(5)[OF `set ss \<inter> signals_of seq = {}` 8(8-9) `sig \<notin> signals_of seq`] by auto 
  moreover have " wp3_fun \<Gamma> (Bcase exp choices) (\<lambda>tw. eval Q [tw[sig, dly :=\<^sub>2 v]] ns ss) = (\<lambda>tw. eval Q [tw[sig, dly :=\<^sub>2 v]] ns ss \<and> wityping \<Gamma> (snd tw))"
    using 8(6)[OF `set ss \<inter> signals_of (Bcase exp choices) = {}` 8(8-9) `sig \<notin> signals_of (Bcase exp choices)`] by auto
  ultimately show ?case 
    by auto
qed

lemma wp3_fun_inv3:
  assumes "seq_wt \<Gamma> seq"
  assumes \<open>set ss \<inter> set (signals_in seq) = {}\<close>
  assumes \<open>highest_idx_form_rwline Q = 1\<close>
  assumes \<open>wf_form_sig Q (length ss) 0\<close>
  assumes \<open>sig \<notin> set (signals_in seq)\<close>
  assumes \<open>sig' \<notin> set (signals_in seq)\<close>
  assumes \<open>sig \<noteq> sig'\<close>
  shows "wp3_fun \<Gamma> seq (\<lambda>tw. eval Q [tw[sig, dly :=\<^sub>2 v][sig', dly' :=\<^sub>2 v']] ns ss) = 
                       (\<lambda>tw. eval Q [tw[sig, dly :=\<^sub>2 v][sig', dly' :=\<^sub>2 v']] ns ss \<and> wityping \<Gamma> (snd tw))"
  using assms
proof (induction seq arbitrary: Q rule:seq_wt.inducts)
  case (1 \<Gamma>)
  then show ?case by auto
next
  case (2 \<Gamma> s1 s2)
  hence *: "wp3_fun \<Gamma> s2 (\<lambda>tw. eval Q [tw[sig, dly :=\<^sub>2 v][sig', dly' :=\<^sub>2 v']] ns ss) = (\<lambda>tw. eval Q [tw[sig, dly :=\<^sub>2 v][sig', dly' :=\<^sub>2 v']] ns ss \<and> wityping \<Gamma> (snd tw))"
    by auto
  have "set ss \<inter> signals_of (s1) = {}" and "sig \<notin> signals_of s1" and "sig' \<notin> signals_of s1"
    using 2 by auto
  have "wp3_fun \<Gamma> (Bcomp s1 s2) (\<lambda>tw. eval Q [tw[sig, dly :=\<^sub>2 v][sig', dly' :=\<^sub>2 v']] ns ss) = 
        wp3_fun \<Gamma> s1 (wp3_fun \<Gamma> s2 (\<lambda>tw. eval Q [tw[sig, dly :=\<^sub>2 v][sig', dly' :=\<^sub>2 v']] ns ss))"
    by auto
  also have "... = wp3_fun \<Gamma> s1 (\<lambda>tw. eval Q [tw[sig, dly :=\<^sub>2 v][sig', dly' :=\<^sub>2 v']] ns ss \<and> wityping \<Gamma> (snd tw))"
    unfolding * by auto
  also have "... = wp3_fun \<Gamma> s1 (\<lambda>tw. eval Q [tw[sig, dly :=\<^sub>2 v][sig', dly' :=\<^sub>2 v']] ns ss)"
    using wp3_fun_unaffected_wityping[OF `seq_wt \<Gamma> s1`] by auto
  also have "... = (\<lambda>tw. eval Q [tw[sig, dly :=\<^sub>2 v][sig', dly' :=\<^sub>2 v']] ns ss \<and> wityping \<Gamma> (snd tw))"
    using 2(3)[OF `set ss \<inter> signals_of s1 = {}` 2(6) 2(7) `sig \<notin> signals_of s1` `sig' \<notin> signals_of s1` `sig \<noteq> sig'`] by auto 
  finally show ?case
    by auto
next
  case (3 \<Gamma> g s1 s2)
  hence "wp3_fun \<Gamma> s1 (\<lambda>tw. eval Q [tw[sig, dly :=\<^sub>2 v][sig', dly' :=\<^sub>2 v']] ns ss) = (\<lambda>tw. eval Q [tw[sig, dly :=\<^sub>2 v][sig', dly' :=\<^sub>2 v']] ns ss \<and> wityping \<Gamma> (snd tw))" and 
        "wp3_fun \<Gamma> s2 (\<lambda>tw. eval Q [tw[sig, dly :=\<^sub>2 v][sig', dly' :=\<^sub>2 v']] ns ss) = (\<lambda>tw. eval Q [tw[sig, dly :=\<^sub>2 v][sig', dly' :=\<^sub>2 v']] ns ss \<and> wityping \<Gamma> (snd tw))"
    by auto
  then show ?case 
    by auto
next
  case (4 \<Gamma> exp sig'' dly'')
  hence "sig'' \<notin> set ss" and "sig'' \<noteq> sig" and "sig'' \<noteq> sig'"
    by auto
  have "\<And>a.  eval Q [a[ sig'', dly'' :=\<^sub>2 eval_world_raw2 a exp][ sig, dly :=\<^sub>2 v][sig', dly' :=\<^sub>2 v']] ns ss = eval Q [a[sig, dly :=\<^sub>2 v][sig', dly' :=\<^sub>2 v']] ns ss"
    using eval_free_vars3[OF `sig'' \<notin> set ss` 4(4) _ `sig'' \<noteq> sig` `sig'' \<noteq> sig'` `sig \<noteq> sig'`] 4(3) by auto 
  thus ?case 
    by auto
next
  case (5 \<Gamma> exp sig'' dly'')
  hence "sig'' \<notin> set ss" and "sig'' \<noteq> sig" and "sig'' \<noteq> sig'" 
    by auto
  have *: "\<And>a.  eval Q [a\<lbrakk> sig'', dly'' :=\<^sub>2 eval_world_raw2 a exp\<rbrakk>[ sig, dly :=\<^sub>2 v][sig', dly' :=\<^sub>2 v']] ns ss = eval Q [a[ sig, dly :=\<^sub>2 v][sig', dly' :=\<^sub>2 v']] ns ss"
    using eval_free_vars_inert3[OF `sig'' \<notin> set ss` 5(4) _ `sig'' \<noteq> sig` `sig \<noteq> sig'` `sig'' \<noteq> sig'`] 5(3) by auto  
  thus ?case 
    by auto
next
  case (6 \<Gamma> exp ty)
  then show ?case by auto
next
  case (7 \<Gamma> exp ty ss choices)
  then show ?case by auto
next
  case (8 \<Gamma> exp ty exp' seq choices)
  hence "set ss \<inter> signals_of seq = {}" and "set ss \<inter> signals_of (Bcase exp choices) = {}" and "sig \<notin> signals_of seq"
  and "sig \<notin> signals_of (Bcase exp choices)" and "sig' \<notin> signals_of seq" and "sig' \<notin> signals_of (Bcase exp choices)"
    by auto
  have "wp3_fun \<Gamma> seq (\<lambda>tw. eval Q [tw[sig, dly :=\<^sub>2 v][sig', dly' :=\<^sub>2 v']] ns ss) = (\<lambda>tw. eval Q [tw[sig, dly :=\<^sub>2 v][sig', dly' :=\<^sub>2 v']] ns ss \<and> wityping \<Gamma> (snd tw))"
    using 8(5)[OF `set ss \<inter> signals_of seq = {}` 8(8-9) `sig \<notin> signals_of seq` `sig' \<notin> signals_of seq` `sig \<noteq> sig'`] by auto 
  moreover have " wp3_fun \<Gamma> (Bcase exp choices) (\<lambda>tw. eval Q [tw[sig, dly :=\<^sub>2 v][sig', dly' :=\<^sub>2 v']] ns ss) = (\<lambda>tw. eval Q [tw[sig, dly :=\<^sub>2 v][sig', dly' :=\<^sub>2 v']] ns ss \<and> wityping \<Gamma> (snd tw))"
    using 8(6)[OF `set ss \<inter> signals_of (Bcase exp choices) = {}` 8(8-9) `sig \<notin> signals_of (Bcase exp choices)` `sig' \<notin> signals_of (Bcase exp choices)` `sig \<noteq> sig'`] 
    by auto
  ultimately show ?case 
    by auto
qed

lemma wp3_fun_inv3':
  assumes "seq_wt \<Gamma> seq"
  assumes \<open>set ss \<inter> set (signals_in seq) = {}\<close>
  assumes \<open>highest_idx_form_rwline Q = 1\<close>
  assumes \<open>wf_form_sig Q (length ss) 0\<close>
  assumes \<open>sig \<notin> set (signals_in seq)\<close>
  assumes \<open>sig' \<notin> set (signals_in seq)\<close>
  assumes \<open>sig \<noteq> sig'\<close>
  assumes \<open>set (signals_in seq) \<inter> set_bexp v = {}\<close> \<open>set (signals_in seq) \<inter> set_bexp v' = {}\<close>
  shows "wp3_fun \<Gamma> seq (\<lambda>tw. eval Q [tw[sig, dly :=\<^sub>2 eval_world_raw2 tw v ][sig', dly' :=\<^sub>2 eval_world_raw2 tw v']] ns ss) = 
                       (\<lambda>tw. eval Q [tw[sig, dly :=\<^sub>2 eval_world_raw2 tw v ][sig', dly' :=\<^sub>2 eval_world_raw2 tw v']] ns ss \<and> wityping \<Gamma> (snd tw))"
  using assms
proof (induction seq arbitrary: Q rule:seq_wt.inducts)
  case (1 \<Gamma>)
  then show ?case by auto
next
  case (2 \<Gamma> s1 s2)
  hence "set ss \<inter> signals_of s1 = {}" and "set ss \<inter> signals_of s2= {}" and "sig \<notin> signals_of s2"
    and "sig' \<notin> signals_of s2" and "signals_of s2 \<inter> set_bexp v = {}" and "signals_of s2 \<inter> set_bexp v' = {}"
    and "signals_of s1 \<inter> set_bexp v = {}" and "signals_of s1 \<inter> set_bexp v' = {}"
    by auto
  have *: "wp3_fun \<Gamma> s2 (\<lambda>tw. eval Q [tw[sig, dly :=\<^sub>2  eval_world_raw2 tw v][sig', dly' :=\<^sub>2 eval_world_raw2 tw v']] ns ss) = 
                         (\<lambda>tw. eval Q [tw[sig, dly :=\<^sub>2  eval_world_raw2 tw v][sig', dly' :=\<^sub>2 eval_world_raw2 tw v']] ns ss \<and> wityping \<Gamma> (snd tw))"
    using 2(4)[OF `set ss \<inter> signals_of s2= {}` 2(6-7) `sig \<notin> signals_of s2` `sig' \<notin> signals_of s2` `sig \<noteq> sig'` `signals_of s2 \<inter> set_bexp v = {}`
                  `signals_of s2 \<inter> set_bexp v' = {}`] by auto
  have "set ss \<inter> signals_of (s1) = {}" and "sig \<notin> signals_of s1" and "sig' \<notin> signals_of s1"
    using 2 by auto
  have "wp3_fun \<Gamma> (Bcomp s1 s2) (\<lambda>tw. eval Q [tw[sig, dly :=\<^sub>2 eval_world_raw2 tw v][sig', dly' :=\<^sub>2 eval_world_raw2 tw v']] ns ss) = 
        wp3_fun \<Gamma> s1 (wp3_fun \<Gamma> s2 (\<lambda>tw. eval Q [tw[sig, dly :=\<^sub>2 eval_world_raw2 tw v][sig', dly' :=\<^sub>2 eval_world_raw2 tw v']] ns ss))"
    by auto
  also have "... = wp3_fun \<Gamma> s1 (\<lambda>tw. eval Q [tw[sig, dly :=\<^sub>2 eval_world_raw2 tw v][sig', dly' :=\<^sub>2  eval_world_raw2 tw v']] ns ss \<and> wityping \<Gamma> (snd tw))"
    unfolding * by auto
  also have "... = wp3_fun \<Gamma> s1 (\<lambda>tw. eval Q [tw[sig, dly :=\<^sub>2 eval_world_raw2 tw v][sig', dly' :=\<^sub>2 eval_world_raw2 tw v']] ns ss)"
    using wp3_fun_unaffected_wityping[OF `seq_wt \<Gamma> s1`] by auto
  also have "... = (\<lambda>tw. eval Q [tw[sig, dly :=\<^sub>2 eval_world_raw2 tw v][sig', dly' :=\<^sub>2 eval_world_raw2 tw v']] ns ss \<and> wityping \<Gamma> (snd tw))"
    using 2(3)[OF `set ss \<inter> signals_of s1 = {}` 2(6) 2(7) `sig \<notin> signals_of s1` `sig' \<notin> signals_of s1` `sig \<noteq> sig'` `signals_of s1 \<inter> set_bexp v = {}`
                  `signals_of s1 \<inter> set_bexp v' = {}`] 
      by auto 
  finally show ?case
    by auto
next
  case (3 \<Gamma> g s1 s2)
  hence "sig \<notin> signals_of s1" and "sig' \<notin> signals_of s1" and "signals_of s1 \<inter> set_bexp v = {}" and "signals_of s1 \<inter> set_bexp v' = {}"
    and "set ss \<inter> signals_of s1 = {}" and "set ss \<inter> signals_of s2 = {}"
    by auto
  hence "wp3_fun \<Gamma> s1 (\<lambda>tw. eval Q [tw[sig, dly :=\<^sub>2 eval_world_raw2 tw v][sig', dly' :=\<^sub>2 eval_world_raw2 tw v']] ns ss) = 
        (\<lambda>tw. eval Q [tw[sig, dly :=\<^sub>2 eval_world_raw2 tw v][sig', dly' :=\<^sub>2 eval_world_raw2 tw v']] ns ss \<and> wityping \<Gamma> (snd tw))" 
    using 3(4)[OF `set ss \<inter> signals_of s1 = {}` 3(7-8) _ _ `sig \<noteq> sig'`] by auto
  have "sig \<notin> signals_of s2" and "sig' \<notin> signals_of s2 " and "signals_of s2 \<inter> set_bexp v = {}" and "signals_of s2 \<inter> set_bexp v' = {}"
    using 3 by auto
  hence "wp3_fun \<Gamma> s2 (\<lambda>tw. eval Q [tw[sig, dly :=\<^sub>2 eval_world_raw2 tw v][sig', dly' :=\<^sub>2 eval_world_raw2 tw v']] ns ss) = 
        (\<lambda>tw. eval Q [tw[sig, dly :=\<^sub>2 eval_world_raw2 tw v][sig', dly' :=\<^sub>2 eval_world_raw2 tw v']] ns ss \<and> wityping \<Gamma> (snd tw))"
    using 3(5)[OF `set ss \<inter> signals_of s2 = {}` 3(7-8) _ _ assms(7)] by auto
  then show ?case 
    by (simp add: \<open>wp3_fun \<Gamma> s1 (\<lambda>tw. eval Q [tw[ sig, dly :=\<^sub>2 eval_world_raw2 tw v][ sig', dly'
    :=\<^sub>2 eval_world_raw2 tw v']] ns ss) = (\<lambda>tw. eval Q [tw[ sig, dly :=\<^sub>2 eval_world_raw2 tw v][
    sig', dly' :=\<^sub>2 eval_world_raw2 tw v']] ns ss \<and> wityping \<Gamma> (snd tw))\<close>)
next
  case (4 \<Gamma> exp sig'' dly'')
  hence "sig'' \<notin> set ss" and "sig'' \<noteq> sig" and "sig'' \<noteq> sig'" and "sig'' \<notin> set_bexp v" and "sig'' \<notin> set_bexp v'"
    by auto
  have *: "\<And>a.  eval Q [a[ sig'', dly'' :=\<^sub>2 eval_world_raw2 a exp][ sig, dly   :=\<^sub>2  eval_world_raw (get_time a) (snd a[ sig'', dly'' :=\<^sub>2 eval_world_raw2 a exp]) v]
                                                                  [ sig', dly' :=\<^sub>2  eval_world_raw (get_time a) (snd a[ sig'', dly'' :=\<^sub>2 eval_world_raw2 a exp]) v']] ns ss = 
             eval Q [a[sig, dly :=\<^sub>2 eval_world_raw2 a[ sig'', dly'' :=\<^sub>2 eval_world_raw2 a exp] v][sig', dly' :=\<^sub>2 eval_world_raw2 a[ sig'', dly'' :=\<^sub>2 eval_world_raw2 a exp] v']] ns ss"
    using eval_free_vars3[OF `sig'' \<notin> set ss` 4(4) _ `sig'' \<noteq> sig` `sig'' \<noteq> sig'` `sig \<noteq> sig'`] 4(3) by auto 
  moreover have **: "\<And>a. eval Q [a[sig, dly :=\<^sub>2 eval_world_raw2 a[ sig'', dly'' :=\<^sub>2 eval_world_raw2 a exp] v][sig', dly' :=\<^sub>2 eval_world_raw2 a[ sig'', dly'' :=\<^sub>2 eval_world_raw2 a exp] v']] ns ss = 
                eval Q  [a[sig, dly :=\<^sub>2 eval_world_raw2 a v][sig', dly' :=\<^sub>2 eval_world_raw2 a v']] ns ss"
    unfolding eval_world_raw2_irrelevant[OF `sig'' \<notin> set_bexp v`] eval_world_raw2_irrelevant[OF `sig'' \<notin> set_bexp v'`] 
    by auto
  ultimately show ?case
    by auto
next
  case (5 \<Gamma> exp sig'' dly'')
  hence "sig'' \<notin> set ss" and "sig'' \<noteq> sig" and "sig'' \<noteq> sig'" and "sig'' \<notin> set_bexp v" and "sig'' \<notin> set_bexp v'"
    by auto
  have *: "\<And>a.  eval Q [a\<lbrakk> sig'', dly'' :=\<^sub>2 eval_world_raw2 a exp\<rbrakk>[ sig, dly   :=\<^sub>2  eval_world_raw2 a\<lbrakk> sig'', dly'' :=\<^sub>2 eval_world_raw2 a exp\<rbrakk> v]
                                                                  [ sig', dly' :=\<^sub>2  eval_world_raw2 a\<lbrakk> sig'', dly'' :=\<^sub>2 eval_world_raw2 a exp\<rbrakk> v']] ns ss = 
                 eval Q [a[sig, dly :=\<^sub>2 eval_world_raw2 a\<lbrakk> sig'', dly'' :=\<^sub>2 eval_world_raw2 a exp\<rbrakk> v][sig', dly' :=\<^sub>2 eval_world_raw2 a\<lbrakk> sig'', dly'' :=\<^sub>2 eval_world_raw2 a exp\<rbrakk> v']] ns ss"
    using eval_free_vars_inert3[OF `sig'' \<notin> set ss` 5(4) _ `sig'' \<noteq> sig` `sig \<noteq> sig'` `sig'' \<noteq> sig'`] 5(3) 
    by (metis One_nat_def Suc_eq_plus1 fst_worldline_inert_upd2 le_numeral_extra(4) list.size(3))
  have **: "\<And>a. eval Q [a[sig, dly :=\<^sub>2 eval_world_raw2 a\<lbrakk> sig'', dly'' :=\<^sub>2 eval_world_raw2 a exp\<rbrakk> v][sig', dly' :=\<^sub>2 eval_world_raw2 a\<lbrakk> sig'', dly'' :=\<^sub>2 eval_world_raw2 a exp\<rbrakk> v']] ns ss = 
                eval Q  [a[sig, dly :=\<^sub>2 eval_world_raw2 a v][sig', dly' :=\<^sub>2 eval_world_raw2 a v']] ns ss"
    unfolding eval_world_raw2_irrelevant_inert[OF `sig'' \<notin> set_bexp v`] eval_world_raw2_irrelevant_inert[OF `sig'' \<notin> set_bexp v'`] by auto 
  thus ?case
    using * by auto
next
  case (6 \<Gamma> exp ty)
  then show ?case by auto
next
  case (7 \<Gamma> exp ty ss choices)
  then show ?case by auto
next
  case (8 \<Gamma> exp ty exp' seq choices)
  hence "set ss \<inter> signals_of seq = {}" and "set ss \<inter> signals_of (Bcase exp choices) = {}" and "sig \<notin> signals_of seq"
  and "sig \<notin> signals_of (Bcase exp choices)" and "sig' \<notin> signals_of seq" and "sig' \<notin> signals_of (Bcase exp choices)"
  and "signals_of seq \<inter> set_bexp v = {}" and "signals_of seq \<inter> set_bexp v' = {}" and "signals_of (Bcase exp choices) \<inter> set_bexp v = {}"
  and "signals_of (Bcase exp choices) \<inter> set_bexp v' = {}"
    by auto
  have "wp3_fun \<Gamma> seq (\<lambda>tw. eval Q [tw[sig, dly :=\<^sub>2 eval_world_raw2 tw v][sig', dly' :=\<^sub>2 eval_world_raw2 tw v']] ns ss) = 
                      (\<lambda>tw. eval Q [tw[sig, dly :=\<^sub>2 eval_world_raw2 tw v][sig', dly' :=\<^sub>2 eval_world_raw2 tw v']] ns ss \<and> wityping \<Gamma> (snd tw))"
    using 8(5)[OF `set ss \<inter> signals_of seq = {}` 8(8-9) `sig \<notin> signals_of seq` `sig' \<notin> signals_of seq` `sig \<noteq> sig'` `signals_of seq \<inter> set_bexp v = {}`
                  `signals_of seq \<inter> set_bexp v' = {}`] 
    by auto
  moreover have " wp3_fun \<Gamma> (Bcase exp choices) (\<lambda>tw. eval Q [tw[sig, dly :=\<^sub>2 eval_world_raw2 tw v][sig', dly' :=\<^sub>2 eval_world_raw2 tw v']] ns ss) = 
                  (\<lambda>tw. eval Q [tw[sig, dly :=\<^sub>2 eval_world_raw2 tw v][sig', dly' :=\<^sub>2 eval_world_raw2 tw v']] ns ss \<and> wityping \<Gamma> (snd tw))"
    using 8(6)[OF `set ss \<inter> signals_of (Bcase exp choices) = {}` 8(8-9) `sig \<notin> signals_of (Bcase exp choices)` `sig' \<notin> signals_of (Bcase exp choices)` `sig \<noteq> sig'`
                  `signals_of (Bcase exp choices) \<inter> set_bexp v = {}` `signals_of (Bcase exp choices) \<inter> set_bexp v' = {}`] 
    by auto
  ultimately show ?case 
    by auto
qed

end