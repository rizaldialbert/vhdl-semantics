(*
 * Copyright 2019, NTU
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 *  Author: Albert Rizaldi, NTU Singapore
 *)

theory Cosine_Generator
  imports VHDL_Hoare_Typed Bits_Int_Aux Cosine_Frac_Approx Fixed_Point
begin

datatype sig = INPUT | OUTPUT | INREADY | OUTREADY | OUTREADY_REG 
  | NEXT_OUTREADYREG | ACCUM | NEXT_ACCUM  | COUNTER | NEXT_COUNTER | FRAC | NEXT_FRAC 
  | COMMON | NEXT_COMMON  | CTR_NEQ_0 | CLK | RST | STATE | NEXT_STATE | SQUARE_TEMP 
  | CTR_MSB  | CTR_LSB  | TERM1

text \<open>State encoding\<close>                                     

abbreviation "S_INIT \<equiv> Bliteral Neu [False, False, False]"
abbreviation "S_WAIT \<equiv> Bliteral Neu [False, False, True ]"
abbreviation "S_PRE  \<equiv> Bliteral Neu [False, True , False]"
abbreviation "S_PROC \<equiv> Bliteral Neu [False, True , True ]"
abbreviation "S_POST \<equiv> Bliteral Neu [True , False, False]"

abbreviation "V_INIT \<equiv> Lv Neu [False, False, False]" 
abbreviation "V_WAIT \<equiv> Lv Neu [False, False, True ]"
abbreviation "V_PRE  \<equiv> Lv Neu [False, True , False]"
abbreviation "V_PROC \<equiv> Lv Neu [False, True , True ]"
abbreviation "V_POST \<equiv> Lv Neu [True , False, False]" 

abbreviation "U_ZERO3  \<equiv>  [False, False, False]"
abbreviation "U_ZERO32 \<equiv>  replicate 32 False"

abbreviation "V_ZERO3   \<equiv> Lv Uns U_ZERO3"
abbreviation "V_ZERO32  \<equiv> Lv Sig U_ZERO32"
abbreviation "V_4       \<equiv> Lv Uns [True, False, False]"
abbreviation "V_3       \<equiv> Lv Uns [False, True, True]"
abbreviation "V_2       \<equiv> Lv Uns [False, True, False]"
abbreviation "V_1       \<equiv> Lv Uns [False, False, True]"
abbreviation "V_0       \<equiv> Lv Uns [False, False, False]"



abbreviation "ONE \<equiv> Bliteral Sig (to_bl (1 :: 32 word))"

locale cosine_locale = 
  fixes \<Gamma> :: "sig tyenv"
  assumes "\<Gamma> INREADY = Bty" and "\<Gamma> OUTREADY = Bty" and "\<Gamma> COUNTER = Lty Uns 3"
          "\<Gamma> CTR_NEQ_0 = Bty" and "\<Gamma> CLK = Bty" and "\<Gamma> RST = Bty" and 
          "\<Gamma> INPUT = Lty Sig 32" and  "\<Gamma> OUTPUT = Lty Sig 32" and "\<Gamma> ACCUM = Lty Sig 32" and 
          "\<Gamma> COMMON = Lty Sig 32" and "\<Gamma> FRAC   = Lty Sig 32" and 
          "\<Gamma> STATE  = Lty Neu 3" and  "\<Gamma> NEXT_STATE = Lty Neu 3" and "\<Gamma> SQUARE_TEMP = Lty Sig 64" and 
          "\<Gamma> TERM1 = Lty Sig 64" and "\<Gamma> OUTREADY_REG = Bty" and "\<Gamma> NEXT_OUTREADYREG = Bty" and 
          "\<Gamma> NEXT_ACCUM = Lty Sig 32" and "\<Gamma> NEXT_FRAC = Lty Sig 32" and "\<Gamma> NEXT_COMMON = Lty Sig 32" and 
          "\<Gamma> CTR_MSB = Bty" and "\<Gamma> CTR_LSB = Bty" and "\<Gamma> NEXT_COUNTER = Lty Uns 3"
begin

definition next_state :: "sig conc_stmt" where
" next_state \<equiv> (process {STATE, INREADY, CTR_NEQ_0} : 
      Bcase (Bsig STATE)    
         [   (Explicit (S_INIT), 
                   Bassign_trans NEXT_STATE (S_WAIT) 1)
         ,   (Explicit (S_WAIT),
                   Bguarded (Bsig INREADY) 
                            (Bassign_trans NEXT_STATE (S_PRE)  1)
                            (Bassign_trans NEXT_STATE (S_WAIT) 1))
         ,   (Explicit (S_PRE),
                   Bassign_trans NEXT_STATE (S_PROC) 1)
         ,   (Explicit (S_PROC),
                   Bguarded (Bsig CTR_NEQ_0) 
                       (Bassign_trans NEXT_STATE (S_PROC) 1) 
                       (Bassign_trans NEXT_STATE (S_POST) 1))
         ,   (Explicit (S_POST), 
                   Bassign_trans NEXT_STATE (S_WAIT) 1)
         ,   (Others, 
                   Bassign_trans NEXT_STATE (S_INIT) 1)])"

lemma conc_stmt_wf_next_state: "conc_stmt_wf next_state"
  unfolding next_state_def  conc_stmt_wf_def by auto

lemma nonneg_delay_conc_next_state [simp]: "nonneg_delay_conc next_state"
  unfolding next_state_def by auto

lemma cwt_ns [simp]: "conc_wt \<Gamma> next_state"
  using cosine_locale_axioms
  unfolding next_state_def cosine_locale_def
  by (auto intro!: conc_wt.intros seq_wt.intros bexp_wt.intros)

definition next_common :: "sig conc_stmt" where
  "next_common \<equiv> (process {STATE, COMMON, INREADY, INPUT, SQUARE_TEMP} : 
      Bcase (Bsig STATE)    
         [   (Explicit (S_WAIT),
                   Bguarded (Bsig INREADY)   (Bassign_trans NEXT_COMMON (Bsig INPUT)  1) 
                                             (Bassign_trans NEXT_COMMON (Bsig COMMON) 1))
         ,   (Explicit (S_PRE),
                   Bassign_trans NEXT_COMMON (Badd (Bnot (Bslice SQUARE_TEMP 62 31)) ONE) 1)
         ,   (Explicit (S_PROC), 
                   Bassign_trans NEXT_COMMON (Badd (Bnot (Bsig COMMON)) ONE) 1)
         ,   (Explicit (S_INIT), 
                   Bassign_trans NEXT_COMMON (Bliteral Sig U_ZERO32) 1)
         ,   (Others, 
                   Bassign_trans NEXT_COMMON (Bsig COMMON) 1)])"

lemma conc_stmt_wf_next_common: "conc_stmt_wf next_common"
  unfolding next_common_def  conc_stmt_wf_def by auto

lemma cwt_nc [simp]: "conc_wt \<Gamma> next_common"
  using cosine_locale_axioms unfolding next_common_def cosine_locale_def
  by (auto intro!: conc_wt.intros seq_wt.intros bexp_wt.intros)
  
lemma nonneg_delay_conc_next_common [simp]: "nonneg_delay_conc next_common"
  unfolding next_common_def by auto

lemma seq_wt_next_common:
  "seq_wt \<Gamma> (get_seq next_common)"
  using cwt_nc  by (metis conc_stmt.sel(4) conc_wt_cases(1) next_common_def)

lemma nonneg_delay_next_common:
  "nonneg_delay (get_seq next_common)"
  using nonneg_delay_conc_next_common  by (simp add: next_common_def)

definition squaring :: "sig conc_stmt" where     
  "squaring \<equiv> (process {COMMON} : 
      Bassign_trans SQUARE_TEMP (Bmult (Bsig COMMON) (Bsig COMMON)) 1)"

lemma conc_stmt_wf_squaring: "conc_stmt_wf squaring"
  unfolding squaring_def  conc_stmt_wf_def by auto

lemma nonneg_delay_conc_squaring [simp]: "nonneg_delay_conc squaring"
  unfolding squaring_def by auto

lemma cwts [simp]: "conc_wt \<Gamma> squaring"
  using cosine_locale_axioms unfolding squaring_def cosine_locale_def
  by (auto intro!: conc_wt.intros seq_wt.intros bexp_wt.intros)

lemma seq_wt_squaring: "seq_wt \<Gamma> (get_seq squaring)"
  using cwts  by (metis conc_stmt.sel(4) conc_wt_cases(1) squaring_def)

lemma nonneg_delay_squaring: "nonneg_delay (get_seq squaring)"
  using nonneg_delay_conc_squaring by (simp add: squaring_def)

definition next_counter :: "sig conc_stmt" where
  "next_counter \<equiv> (process {STATE, INREADY, CTR_NEQ_0, COUNTER} : 
      Bcase (Bsig STATE)    
         [   (Explicit (S_WAIT),
                   Bguarded (Bsig INREADY) 
                            (Bassign_trans NEXT_COUNTER (Bliteral Uns (to_bl (4 :: 3 word)))  1)
                            (Bassign_trans NEXT_COUNTER (Bsig COUNTER) 1))
         ,   (Explicit (S_PRE),
                   Bassign_trans NEXT_COUNTER (Bsub (Bsig COUNTER) (Bliteral Uns (to_bl (1 ::3 word)))) 1)
         ,   (Explicit (S_PROC),                       
                   Bguarded (Bsig CTR_NEQ_0)           
                       (Bassign_trans NEXT_COUNTER (Bsub (Bsig COUNTER) (Bliteral Uns (to_bl (1 :: 3 word)))) 1) 
                       (Bassign_trans NEXT_COUNTER (Bsig COUNTER) 1))  
         ,   (Explicit (S_INIT), 
                   Bassign_trans NEXT_COUNTER (Bliteral Uns (to_bl (0 :: 3 word))) 1)
         ,   (Others, 
                   Bassign_trans NEXT_COUNTER (Bsig COUNTER) 1)])"

lemma conc_stmt_wf_next_counter: "conc_stmt_wf next_counter"
  unfolding next_counter_def  conc_stmt_wf_def by auto

lemma nonneg_delay_conc_next_counter [simp]: "nonneg_delay_conc next_counter"
  unfolding next_counter_def by auto

lemma cwt_ncnt [simp]: "conc_wt \<Gamma> next_counter"
  using cosine_locale_axioms unfolding next_counter_def cosine_locale_def
  by (intro conc_wt.intros seq_wt.intros bexp_wt.intros) auto

lemma seq_wt_next_counter: "seq_wt \<Gamma> (get_seq next_counter)"
  using cwt_ncnt by (metis conc_stmt.sel(4) conc_wt_cases(1) next_counter_def)

lemma nonneg_delay_next_counter: "nonneg_delay (get_seq next_counter)"
  using nonneg_delay_conc_next_counter by (auto simp add: next_counter_def)

definition next_accum :: "sig conc_stmt" where
  "next_accum \<equiv> (process {STATE, ACCUM, FRAC, TERM1} : 
      Bcase (Bsig STATE)
         [   (Explicit (S_PRE),
                   Bassign_trans NEXT_ACCUM (Bliteral Sig (to_bl (0 :: 32 word))) 1)
         ,   (Explicit (S_PROC),
                   Bassign_trans NEXT_ACCUM (Badd (Bsig FRAC) (Bslice TERM1 62 31)) 1)
         ,   (Explicit (S_INIT), 
                   Bassign_trans NEXT_ACCUM (Bliteral Sig (to_bl (0 :: 32 word))) 1)
         ,   (Others,
                   Bassign_trans NEXT_ACCUM (Bsig ACCUM) 1)])"

lemma conc_stmt_wf_next_accum: "conc_stmt_wf next_accum"
  unfolding next_accum_def  conc_stmt_wf_def by auto

lemma nonneg_delay_conc_next_accum [simp]: "nonneg_delay_conc next_accum"
  unfolding next_accum_def by auto

lemma cwt_na [simp]: "conc_wt \<Gamma> next_accum"
  using cosine_locale_axioms unfolding cosine_locale_def next_accum_def
  by (intro conc_wt.intros seq_wt.intros bexp_wt.intros) auto

lemma seq_wt_next_accum: "seq_wt \<Gamma> (get_seq next_accum)"
  using cwt_na by (metis conc_stmt.sel(4) conc_wt_cases(1) next_accum_def)

lemma nonneg_delay_next_accum: "nonneg_delay (get_seq next_accum)"
  using nonneg_delay_conc_next_accum by (simp add: next_accum_def)
  
definition term1 :: "sig conc_stmt" where
  "term1 \<equiv> ( process {COMMON, ACCUM} : 
      Bassign_trans TERM1 (Bmult (Bsig COMMON) (Bsig ACCUM)) 1)"

lemma conc_stmt_wf_term1: "conc_stmt_wf term1"
  unfolding term1_def  conc_stmt_wf_def by auto

lemma nonneg_delay_conc_term1 [simp]: "nonneg_delay_conc term1"
  unfolding term1_def by auto

lemma cwt_t1[simp]: "conc_wt \<Gamma> term1"
  using cosine_locale_axioms unfolding cosine_locale_def term1_def
  by (intro conc_wt.intros seq_wt.intros bexp_wt.intros) auto

lemma seq_wt_term1: "seq_wt \<Gamma> (get_seq term1)"
  using cwt_t1 by (metis conc_stmt.sel(4) conc_wt_cases(1) term1_def)

lemma nonneg_delay_term1: "nonneg_delay (get_seq term1)"
  using nonneg_delay_conc_term1 by (simp add: term1_def)

definition next_frac :: "sig conc_stmt" where
  "next_frac \<equiv> (process {COUNTER} : 
      Bcase (Bsig COUNTER) 
         [   (Explicit (Bliteral Uns (to_bl (4 :: 3 word))), 
                   Bassign_trans NEXT_FRAC (Bliteral Sig (to_bl (approx_eighth :: 32 word))) 1)
         ,   (Explicit (Bliteral Uns (to_bl (3 :: 3 word))), 
                   Bassign_trans NEXT_FRAC (Bliteral Sig (to_bl (approx_sixth  :: 32 word))) 1)
         ,   (Explicit (Bliteral Uns (to_bl (2 :: 3 word))), 
                   Bassign_trans NEXT_FRAC (Bliteral Sig (to_bl (approx_fourth :: 32 word))) 1)
         ,   (Explicit (Bliteral Uns (to_bl (1 :: 3 word))), 
                   Bassign_trans NEXT_FRAC (Bliteral Sig (to_bl (approx_half   :: 32 word))) 1)
         ,   (Explicit (Bliteral Uns (to_bl (0 :: 3 word))), 
                   Bassign_trans NEXT_FRAC (Bliteral Sig (to_bl (approx_one    :: 32 word))) 1)
         ,   (Others, 
                   Bassign_trans NEXT_FRAC (Bliteral Sig (to_bl (0 :: 32 word))) 1) ])"

lemma conc_stmt_wf_next_frac: "conc_stmt_wf next_frac"
  unfolding next_frac_def  conc_stmt_wf_def by auto

lemma nonneg_delay_conc_next_frac [simp]: "nonneg_delay_conc next_frac"
  unfolding next_frac_def by auto

lemma cwt_nf [simp]: "conc_wt \<Gamma> next_frac"
  using cosine_locale_axioms unfolding cosine_locale_def next_frac_def
  by (intro conc_wt.intros seq_wt.intros bexp_wt.intros) auto 

lemma seq_wt_next_frac: "seq_wt \<Gamma> (get_seq next_frac)"
  using cwt_nf by (metis conc_stmt.sel(4) conc_wt_cases(1) next_frac_def)

lemma nonneg_delay_next_frac: "nonneg_delay (get_seq next_frac)"
  using nonneg_delay_conc_next_frac by (simp add: next_frac_def)

definition next_outready_reg :: "sig conc_stmt" where
  "next_outready_reg \<equiv> (process {STATE, CTR_NEQ_0, OUTREADY_REG} : 
      Bcase (Bsig STATE)    
         [   (Explicit (S_PROC), 
                    Bguarded (Bsig CTR_NEQ_0) 
                        (Bassign_trans NEXT_OUTREADYREG (Bfalse) 1) 
                        (Bassign_trans NEXT_OUTREADYREG (Btrue ) 1))
         ,   (Explicit (S_POST), 
                    Bassign_trans NEXT_OUTREADYREG (Bsig OUTREADY_REG) 1)
         ,   (Others, 
                    Bassign_trans NEXT_OUTREADYREG (Bfalse) 1)])"

lemma conc_stmt_wf_next_outready_reg: "conc_stmt_wf next_outready_reg"
  unfolding next_outready_reg_def  conc_stmt_wf_def by auto

lemma nonneg_delay_conc_next_outready_reg [simp]: "nonneg_delay_conc next_outready_reg"
  unfolding next_outready_reg_def by auto

lemma cwt_no [simp]: "conc_wt \<Gamma> next_outready_reg"
  using cosine_locale_axioms unfolding cosine_locale_def next_outready_reg_def
  by (auto intro!: conc_wt.intros seq_wt.intros bexp_wt.intros)

lemma seq_wt_next_outready_reg: "seq_wt \<Gamma> (get_seq next_outready_reg)"
  using cwt_no by (metis conc_stmt.sel(4) conc_wt_cases(1) next_outready_reg_def)

lemma nonneg_delay_next_outready_reg: "nonneg_delay (get_seq next_outready_reg)"
  using nonneg_delay_conc_next_outready_reg by (auto simp add: next_outready_reg_def)

definition "ctr_neq_0 \<equiv> (process {COUNTER} : 
  Bassign_trans CTR_NEQ_0 (Bor (Bindex COUNTER 2) (Bor (Bindex COUNTER 1) (Bindex COUNTER 0))) 1)"

lemma conc_stmt_wf_ctr_neq_0: "conc_stmt_wf ctr_neq_0"
  unfolding ctr_neq_0_def  conc_stmt_wf_def by auto

lemma nonneg_delay_conc_ctr_neq_0 [simp]: "nonneg_delay_conc ctr_neq_0"
  unfolding ctr_neq_0_def by auto

lemma cwt_n0 [simp]: "conc_wt \<Gamma> ctr_neq_0"
  using cosine_locale_axioms unfolding cosine_locale_def ctr_neq_0_def
  by (auto intro!: conc_wt.intros seq_wt.intros bexp_wt.intros)

lemma seq_wt_ctr_neq_0: "seq_wt \<Gamma> (get_seq ctr_neq_0)"
  using cwt_n0 by (metis conc_stmt.sel(4) conc_wt_cases(1) ctr_neq_0_def)

lemma nonneg_delay_ctr_neq_0: "nonneg_delay (get_seq ctr_neq_0)"
  using nonneg_delay_conc_ctr_neq_0 by (auto simp add: ctr_neq_0_def)
                        
definition "output \<equiv> (process {ACCUM} : 
  Bassign_trans OUTPUT (Bsig ACCUM) 1)"

lemma conc_stmt_wf_output: "conc_stmt_wf output"
  unfolding output_def  conc_stmt_wf_def by auto

lemma nonneg_delay_conc_output [simp]: "nonneg_delay_conc output"
  unfolding output_def by auto

lemma cwt_output[simp]: "conc_wt \<Gamma> output"
  using cosine_locale_axioms unfolding cosine_locale_def output_def
  by (auto intro!: conc_wt.intros seq_wt.intros bexp_wt.intros)

lemma seq_wt_output: "seq_wt \<Gamma> (get_seq output)"
  using cwt_output by (metis conc_stmt.sel(4) conc_wt_cases(1) output_def)

lemma nonneg_delay_output: "nonneg_delay (get_seq output)"
  using nonneg_delay_conc_output  by (simp add: output_def)

definition "output_ready \<equiv> (process {OUTREADY_REG} : 
  Bassign_trans OUTREADY (Bsig OUTREADY_REG) 1)"

lemma conc_stmt_wf_output_ready: "conc_stmt_wf output_ready"
  unfolding output_ready_def  conc_stmt_wf_def by auto

lemma nonneg_delay_conc_output_ready [simp]: "nonneg_delay_conc output_ready"
  unfolding output_ready_def by auto

lemma cwt_outready[simp]: "conc_wt \<Gamma> output_ready"
  using cosine_locale_axioms unfolding cosine_locale_def output_ready_def
  by (auto intro!: conc_wt.intros seq_wt.intros bexp_wt.intros)

lemma seq_wt_output_ready: "seq_wt \<Gamma> (get_seq output_ready)"
  using cwt_outready by (metis conc_stmt.sel(4) conc_wt_cases(1) output_ready_def)

lemma nonneg_delay_output_ready: "nonneg_delay (get_seq output_ready)"
  using nonneg_delay_conc_output_ready by (auto simp add: output_ready_def)

definition "registers \<equiv> (process {CLK} : 
              Bguarded (Band (Bsig CLK) (Bsig_event CLK)) 
                (Bguarded (Bsig RST) 
                    (Bcomp (Bassign_trans ACCUM        (Bliteral Sig U_ZERO32) 1)      
                    (Bcomp (Bassign_trans COUNTER      (Bliteral Uns U_ZERO3 ) 1)      
                    (Bcomp (Bassign_trans FRAC         (Bliteral Sig U_ZERO32) 1) 
                    (Bcomp (Bassign_trans COMMON       (Bliteral Sig U_ZERO32) 1) 
                    (Bcomp (Bassign_trans STATE        (S_INIT)                1)
                           (Bassign_trans OUTREADY_REG (Bfalse)                1))))))

                    (Bcomp (Bassign_trans ACCUM        (Bsig NEXT_ACCUM)       1)     
                    (Bcomp (Bassign_trans COUNTER      (Bsig NEXT_COUNTER)     1)     
                    (Bcomp (Bassign_trans FRAC         (Bsig NEXT_FRAC)        1) 
                    (Bcomp (Bassign_trans COMMON       (Bsig NEXT_COMMON)      1) 
                    (Bcomp (Bassign_trans STATE        (Bsig NEXT_STATE)       1)
                           (Bassign_trans OUTREADY_REG (Bsig NEXT_OUTREADYREG) 1))))))) 
                (Bnull))"

lemma nonneg_delay_conc_registers [simp]: "nonneg_delay_conc registers"
  unfolding registers_def by auto

lemma cwt_reg [simp]: "conc_wt \<Gamma> registers"
  using cosine_locale_axioms unfolding cosine_locale_def registers_def
  by (auto intro!: conc_wt.intros seq_wt.intros bexp_wt.intros)

lemma conc_stmt_wf_registers: "conc_stmt_wf registers"
  unfolding registers_def  conc_stmt_wf_def by auto

definition architecture :: "sig conc_stmt" where
  "architecture \<equiv>     
                    registers  || next_state || next_common || squaring           || next_counter 
                ||  next_accum || term1      || next_frac   || next_outready_reg  ||  ctr_neq_0   
                || output      || output_ready"

lemma nonneg_delay_conc_architecture : "nonneg_delay_conc architecture"
  unfolding architecture_def by auto

lemmas circuit_defs = registers_def next_state_def next_common_def squaring_def next_counter_def
next_accum_def term1_def next_frac_def next_outready_reg_def ctr_neq_0_def 
output_def output_ready_def

lemma conc_stmt_wf_arch: "conc_stmt_wf architecture"
  unfolding architecture_def circuit_defs conc_stmt_wf_def by auto

lemma [simp]: "conc_wt \<Gamma> architecture"
  using cosine_locale_axioms unfolding cosine_locale_def architecture_def
  by (auto intro!: conc_wt.intros)

abbreviation "clk_period \<equiv> 10 :: nat"

(* fun approx_div_fact :: "nat \<Rightarrow> (1, 31) fixed" where
  "approx_div_fact 0                          = Fixed (approx_one :: (1 + 31) word)   "
| "approx_div_fact (Suc 0)                    = Fixed (approx_half :: (1 + 31) word)  "
| "approx_div_fact (Suc (Suc 0))              = Fixed (approx_fourth :: (1 + 31) word)"
| "approx_div_fact (Suc (Suc (Suc 0)))        = Fixed (approx_sixth :: (1 + 31) word) "
| "approx_div_fact (Suc (Suc (Suc (Suc 0))))  = Fixed (approx_eighth :: (1 + 31) word)"

fun fixed_of_sval :: "val \<Rightarrow> ('a::len0, 'b::len0) fixed" where
  "fixed_of_sval (Lv ki bl) = Fixed (of_bl bl :: ('a + 'b) word)"

fun nat_of_val :: "val \<Rightarrow> nat" where
  "nat_of_val (Lv ki bl) = nat (bl_to_bin bl)"

declare [[coercion nat_of_val]]

fun val_of_fixed :: "('a::len0, 'b::len0) fixed \<Rightarrow> val" where
  "val_of_fixed fi = Lv Sig (to_bl (word_of_fixed fi))"

definition inv :: "sig assn2" where
  "inv tw =   ( is_posedge2 (snd tw) CLK (fst tw - 1)  \<and> (wline_of tw STATE (fst tw) = V_PROC \<or> wline_of tw STATE (fst tw) = V_POST)  \<longrightarrow> 
                fixed_of_sval (wline_of tw ACCUM (fst tw)) = 
                    (foldr (\<lambda>a b. approx_div_fact a + fixed_of_sval (wline_of tw COMMON (fst tw)) * b) [(wline_of tw COUNTER (fst tw)) ..< 5]  0))"

definition inv_common :: "sig assn2" where
  "inv_common tw = ( is_posedge2 (snd tw) CLK (fst tw - 1) \<and> (wline_of tw STATE (fst tw) = V_POST) \<longrightarrow> 
                (fixed_of_sval (wline_of tw COMMON (fst tw)) :: (1,31) fixed) =   square_fixed (fixed_of_sval (wline_of tw COMMON (fst tw - 5 * clk_period))))"

definition inv_common_even :: "sig assn2" where
  "inv_common_even tw = ( let ctr ::nat = wline_of tw COUNTER (fst tw) in 
                    is_posedge2 (snd tw) CLK (fst tw - 1) \<and> (wline_of tw STATE (fst tw) = V_PROC) \<and> even ctr \<longrightarrow> 
                (fixed_of_sval (wline_of tw COMMON (fst tw)) :: (1,31) fixed) = - square_fixed (fixed_of_sval (wline_of tw COMMON (fst tw - ctr * clk_period))))"

definition inv_common_odd :: "sig assn2" where
  "inv_common_odd tw = ( let ctr :: nat = wline_of tw COUNTER (fst tw) in 
                    is_posedge2 (snd tw) CLK (fst tw - 1) \<and> (wline_of tw STATE (fst tw) = V_PROC) \<and> odd ctr \<longrightarrow>
                (fixed_of_sval (wline_of tw COMMON (fst tw)) :: (1,31) fixed) =   square_fixed (fixed_of_sval (wline_of tw COMMON (fst tw - ctr * clk_period))))"

lemma cswf3: "conc_stmt_wf (registers || local.next_state || next_common)"
    unfolding conc_stmt_wf_def circuit_defs by auto

lemma ndc3: "nonneg_delay_conc (registers || local.next_state ||  next_common) "
    unfolding circuit_defs by auto

lemma cwt3: "conc_wt \<Gamma> (registers || local.next_state || next_common )"
  using cosine_locale_axioms by (auto intro!: conc_wt.intros)

lemma cswf2: "conc_stmt_wf (local.next_state || next_common)"
    unfolding conc_stmt_wf_def circuit_defs by auto

lemma ndc2: "nonneg_delay_conc (local.next_state ||  next_common) "
    unfolding circuit_defs by auto

lemma cwt2: "conc_wt \<Gamma> (local.next_state || next_common )"
    using cosine_locale_axioms by (auto intro!: conc_wt.intros)



lemma wp3_fun_inv_common:
  assumes "sig \<noteq> CLK" and "sig \<noteq> STATE" and "sig \<noteq> COMMON"
  shows "wp3_fun \<Gamma> (Bassign_trans sig expr n) (\<lambda>tw. inv_common (get_time tw + 1, snd tw)) = (\<lambda>tw. wityping \<Gamma> (snd tw) \<and> inv_common (get_time tw + 1, snd tw))"
  unfolding wp3_fun.simps inv_common_def snd_conv fst_conv fst_worldline_upd2 snd_worldline_upd2[OF `sig \<noteq> CLK`] comp_def
  snd_worldline_upd2[OF `sig \<noteq> STATE`] snd_worldline_upd2[OF `sig \<noteq> COMMON`] by auto

lemma wp3_fun_init_state:
  "wp3_fun \<Gamma> (Bassign_trans STATE S_INIT 1) (\<lambda>tw. wityping \<Gamma> (snd tw) \<and> inv_common (fst tw + 1, snd tw)) = 
                                            (\<lambda>tw. wityping \<Gamma> (snd tw))"
proof - 
  have "\<And>tw. type_of (eval_world_raw2 tw S_INIT) = \<Gamma> STATE"
    using cosine_locale_axioms unfolding eval_world_raw.simps cosine_locale_def by (auto)
  hence *: "\<And>tw. wityping \<Gamma> (snd tw) \<Longrightarrow> wityping \<Gamma> (snd tw[ STATE, 1 :=\<^sub>2 eval_world_raw2 tw S_INIT])"
    using worldline_upd_preserve_wityping
    by (simp add: worldline_upd_preserve_wityping worldline_upd2_def)  
  have "\<And>tw. inv_common (get_time tw[ STATE, 1 :=\<^sub>2 eval_world_raw2 tw S_INIT] + 1, snd tw[ STATE, 1 :=\<^sub>2 eval_world_raw2 tw S_INIT]) = True"
    unfolding inv_common_def by (auto simp add: worldline_upd2_def worldline_upd_def)
  with * show ?thesis
    unfolding wp3_fun.simps by auto
qed

lemma wp3_fun_init_sig:
  assumes "sig = COMMON \<or> sig = FRAC \<or> sig = ACCUM"
  shows "wp3_fun \<Gamma> (Bassign_trans sig (Bliteral Sig U_ZERO32) 1) (\<lambda>tw. wityping \<Gamma> (snd tw)) = (\<lambda>tw. wityping \<Gamma> (snd tw))"
proof -
  have *: "\<And>tw. type_of (eval_world_raw2 tw (Bliteral Sig U_ZERO32)) = \<Gamma> sig"
    using cosine_locale_axioms assms unfolding eval_world_raw.simps cosine_locale_def by (auto)
  hence "\<And>tw. wityping \<Gamma> (snd tw) \<Longrightarrow> wityping \<Gamma> (snd tw[ sig, 1 :=\<^sub>2 eval_world_raw2 tw (Bliteral Sig U_ZERO32)])"
    using worldline_upd_preserve_wityping by (simp add: worldline_upd_preserve_wityping worldline_upd2_def) 
  thus ?thesis
    using assms unfolding wp3_fun.simps by auto
qed

lemma wp3_fun_init_common:
  "wp3_fun \<Gamma> (Bassign_trans COMMON (Bliteral Sig U_ZERO32) 1) (\<lambda>tw. wityping \<Gamma> (snd tw)) = (\<lambda>tw. wityping \<Gamma> (snd tw))"
  using wp3_fun_init_sig by auto

lemma wp3_fun_init_frac:
  "wp3_fun \<Gamma> (Bassign_trans FRAC (Bliteral Sig U_ZERO32) 1) (\<lambda>tw. wityping \<Gamma> (snd tw)) = (\<lambda>tw. wityping \<Gamma> (snd tw))"
  using wp3_fun_init_sig by auto

lemma wp3_fun_init_accum:
  "wp3_fun \<Gamma> (Bassign_trans ACCUM (Bliteral Sig U_ZERO32) 1) (\<lambda>tw. wityping \<Gamma> (snd tw)) = (\<lambda>tw. wityping \<Gamma> (snd tw))"
  using wp3_fun_init_sig by auto

lemma wp3_fun_init_counter:
  "wp3_fun \<Gamma> (Bassign_trans COUNTER (Bliteral Uns U_ZERO3) 1) (\<lambda>tw. wityping \<Gamma> (snd tw)) = (\<lambda>tw. wityping \<Gamma> (snd tw))"
proof -
  have *: "\<And>tw. type_of (eval_world_raw2 tw (Bliteral Uns U_ZERO3)) = \<Gamma> COUNTER"
    using cosine_locale_axioms unfolding eval_world_raw.simps cosine_locale_def by (auto)
  hence "\<And>tw. wityping \<Gamma> (snd tw) \<Longrightarrow> wityping \<Gamma> (snd tw[ COUNTER, 1 :=\<^sub>2 eval_world_raw2 tw (Bliteral Uns U_ZERO3)])"
    using worldline_upd_preserve_wityping by (simp add: worldline_upd_preserve_wityping worldline_upd2_def)   
  thus ?thesis
    unfolding wp3_fun.simps by auto
qed

lemma wp3_fun_state_next_state:
  "wp3_fun \<Gamma> (Bassign_trans STATE (Bsig NEXT_STATE) 1) (\<lambda>tw. wityping \<Gamma> (snd tw) \<and> inv_common (fst tw + 1, snd tw)) = 
                                                       (\<lambda>tw. wityping \<Gamma> (snd tw) \<and> inv_common (fst tw + 1, snd tw[STATE, fst tw + 1 := eval_world_raw2 tw (Bsig NEXT_STATE)]))"
proof -
  have "\<And>tw. wityping \<Gamma> (snd tw) \<Longrightarrow> type_of (eval_world_raw2 tw (Bsig NEXT_STATE)) = \<Gamma> STATE"
    using cosine_locale_axioms unfolding eval_world_raw.simps cosine_locale_def wityping_def wtyping_def
    by auto
  hence *: "\<And>tw. wityping \<Gamma> (snd tw) \<Longrightarrow> wityping \<Gamma> (snd tw[ STATE, 1 :=\<^sub>2 eval_world_raw2 tw (Bsig NEXT_STATE)])"
    using worldline_upd_preserve_wityping by (simp add: worldline_upd_preserve_wityping worldline_upd2_def) 
  thus ?thesis
    unfolding wp3_fun.simps fst_worldline_upd2 worldline_upd2_def by auto
qed

lemma wp3_fun_common_next_common:
  "wp3_fun \<Gamma> (Bassign_trans COMMON (Bsig NEXT_COMMON) 1) 
      (\<lambda>tw. wityping \<Gamma> (snd tw) \<and> inv_common (get_time tw + 1, snd tw[STATE, get_time tw + 1:= eval_world_raw2 tw (Bsig NEXT_STATE)])) = 
      (\<lambda>tw. wityping \<Gamma> (snd tw) \<and> inv_common (get_time tw + 1, snd tw[COMMON, fst tw + 1 := eval_world_raw2 tw (Bsig NEXT_COMMON)][STATE, get_time tw + 1:= eval_world_raw2 tw (Bsig NEXT_STATE)]))"
proof -
  have "\<And>tw. wityping \<Gamma> (snd tw) \<Longrightarrow> type_of (eval_world_raw2 tw (Bsig NEXT_COMMON)) = \<Gamma> COMMON"
    using cosine_locale_axioms unfolding eval_world_raw.simps cosine_locale_def wityping_def wtyping_def
    by auto
  hence *: "\<And>tw. wityping \<Gamma> (snd tw) \<Longrightarrow> wityping \<Gamma> (snd tw[ COMMON, 1 :=\<^sub>2 eval_world_raw2 tw (Bsig NEXT_COMMON)])"
    using worldline_upd_preserve_wityping by (simp add: worldline_upd_preserve_wityping worldline_upd2_def) 
  thus ?thesis
    unfolding wp3_fun.simps fst_worldline_upd2 fst_conv snd_conv worldline_upd2_def eval_world_raw.simps worldline_upd_def
    by auto
qed

abbreviation "wp_temp \<equiv> (\<lambda>tw. inv_common (get_time tw + 1, snd tw[COMMON, fst tw + 1 := eval_world_raw2 tw (Bsig NEXT_COMMON)][STATE, get_time tw + 1:= eval_world_raw2 tw (Bsig NEXT_STATE)]))" 

lemma wp3_fun_helper:
  assumes "sig = FRAC \<or> sig = ACCUM" and "next_sig = NEXT_FRAC \<or> next_sig = NEXT_ACCUM"
  shows "wp3_fun \<Gamma> (Bassign_trans sig (Bsig next_sig) 1) (\<lambda>tw. wityping \<Gamma> (snd tw) \<and> wp_temp tw) = (\<lambda>tw. wityping \<Gamma> (snd tw) \<and> wp_temp tw)"
proof -
  have "\<And>tw. wityping \<Gamma> (snd tw) \<Longrightarrow> type_of (eval_world_raw2 tw (Bsig next_sig)) = \<Gamma> sig"
    using cosine_locale_axioms assms unfolding eval_world_raw.simps cosine_locale_def wityping_def wtyping_def
    by auto    
  hence *: "\<And>tw. wityping \<Gamma> (snd tw) \<Longrightarrow> wityping \<Gamma> (snd tw[ sig, 1 :=\<^sub>2 eval_world_raw2 tw (Bsig next_sig)])"
    using worldline_upd_preserve_wityping by (simp add: worldline_upd_preserve_wityping worldline_upd2_def) 
  have "sig \<noteq> NEXT_COMMON" and "sig \<noteq> NEXT_STATE" and "sig \<noteq> CLK"
    using assms by auto
  moreover have "\<And>tw. inv_common
           (get_time tw + 1, snd tw[ sig, 1 :=\<^sub>2 eval_world_raw2 tw (Bsig next_sig)][COMMON, get_time tw[ sig, 1 :=\<^sub>2 eval_world_raw2 tw (Bsig next_sig)] +
                                                      1:= eval_world_raw2 tw[ sig, 1 :=\<^sub>2 eval_world_raw2 tw (Bsig next_sig)]
                                                           (Bsig
                                                             NEXT_COMMON)][STATE, get_time tw[ sig, 1 :=\<^sub>2 eval_world_raw2 tw (Bsig next_sig)] +
                                                                                  1:= eval_world_raw2 tw[ sig, 1 :=\<^sub>2 eval_world_raw2 tw (Bsig next_sig)] (Bsig NEXT_STATE)]) = wp_temp tw"
    unfolding fst_worldline_upd2 eval_world_raw.simps  snd_worldline_upd2[OF `sig \<noteq> NEXT_COMMON`] snd_worldline_upd2[OF `sig \<noteq> NEXT_STATE`]
      inv_common_def snd_conv fst_conv comp_def worldline_upd2_def worldline_upd_def by (auto simp add: assms)
  thus ?thesis
    unfolding wp3_fun.simps using * by auto
qed

lemma wp3_fun_helper_next_frac:
  "wp3_fun \<Gamma> (Bassign_trans FRAC (Bsig NEXT_FRAC) 1) (\<lambda>tw. wityping \<Gamma> (snd tw) \<and> wp_temp tw) = (\<lambda>tw. wityping \<Gamma> (snd tw) \<and> wp_temp tw)"
  using wp3_fun_helper by auto

lemma wp3_fun_helper_next_accum:
  "wp3_fun \<Gamma> (Bassign_trans ACCUM (Bsig NEXT_ACCUM) 1) (\<lambda>tw. wityping \<Gamma> (snd tw) \<and> wp_temp tw) = (\<lambda>tw. wityping \<Gamma> (snd tw) \<and> wp_temp tw)"
  using wp3_fun_helper by auto

lemma wp3_fun_helper_counter:
  shows "wp3_fun \<Gamma> (Bassign_trans COUNTER (Bsig NEXT_COUNTER) 1) (\<lambda>tw. wityping \<Gamma> (snd tw) \<and> wp_temp tw) = (\<lambda>tw. wityping \<Gamma> (snd tw) \<and> wp_temp tw)"
proof -
  have "\<And>tw. wityping \<Gamma> (snd tw) \<Longrightarrow> type_of (eval_world_raw2 tw (Bsig NEXT_COUNTER)) = \<Gamma> COUNTER"
    using cosine_locale_axioms unfolding eval_world_raw.simps cosine_locale_def wityping_def wtyping_def
    by auto    
  hence *: "\<And>tw. wityping \<Gamma> (snd tw) \<Longrightarrow> wityping \<Gamma> (snd tw[ COUNTER, 1 :=\<^sub>2 eval_world_raw2 tw (Bsig NEXT_COUNTER)])"
    using worldline_upd_preserve_wityping by (simp add: worldline_upd_preserve_wityping worldline_upd2_def) 
  have "COUNTER \<noteq> NEXT_COMMON" and "COUNTER \<noteq> NEXT_STATE" and "COUNTER \<noteq> CLK"
    by auto
  moreover have "\<And>tw. inv_common
           (get_time tw + 1, snd tw[ COUNTER, 1 :=\<^sub>2 eval_world_raw2 tw (Bsig NEXT_COUNTER)][COMMON, get_time tw[ COUNTER, 1 :=\<^sub>2 eval_world_raw2 tw (Bsig NEXT_COUNTER)] +
                                                      1:= eval_world_raw2 tw[ COUNTER, 1 :=\<^sub>2 eval_world_raw2 tw (Bsig NEXT_COUNTER)]
                                                           (Bsig
                                                             NEXT_COMMON)][STATE, get_time tw[ COUNTER, 1 :=\<^sub>2 eval_world_raw2 tw (Bsig NEXT_COUNTER)] +
                                                                                  1:= eval_world_raw2 tw[ COUNTER, 1 :=\<^sub>2 eval_world_raw2 tw (Bsig NEXT_COUNTER)] (Bsig NEXT_STATE)]) = wp_temp tw"
    unfolding fst_worldline_upd2 eval_world_raw.simps  snd_worldline_upd2[OF `COUNTER \<noteq> NEXT_COMMON`] snd_worldline_upd2[OF `COUNTER \<noteq> NEXT_STATE`]
      inv_common_def snd_conv fst_conv comp_def worldline_upd2_def worldline_upd_def by (auto)
  thus ?thesis
    unfolding wp3_fun.simps using * by auto
qed


lemma
  shows " \<forall>w. wityping \<Gamma> (snd w) \<and> inv_common w \<longrightarrow> wp3_conc \<Gamma> (registers) (\<lambda>tw. inv_common (get_time tw + 1, snd tw)) w"
  unfolding wp3_conc_single'[OF cwt_reg[unfolded registers_def] nonneg_delay_conc_registers[unfolded registers_def], folded registers_def] 
  wp3_fun.simps(7) wp3_fun.simps(8)  wp3_fun_inv_common[OF sig.simps(185) sig.simps(189) sig.simps(179)]
  wp3_fun_init_state wp3_fun_init_common  wp3_fun_init_frac wp3_fun_init_counter wp3_fun_init_accum
  wp3_fun_state_next_state wp3_fun_common_next_common wp3_fun_helper_next_frac wp3_fun_helper_counter
  wp3_fun_helper_next_accum wp3_fun.simps(1)





theorem
  "\<Gamma> \<turnstile>\<^sub>s \<lbrace>inv_common\<rbrace> registers || next_common || next_state \<lbrace>inv_common\<rbrace>"
  apply (rule While_Suc)
  apply (rule Conseq'[where P="wp3_conc \<Gamma> (registers || next_common || next_state) (\<lambda>tw. inv_common  (fst tw + 1, snd tw))", rotated])
proof (rule wp3_conc_is_pre)
  show "conc_stmt_wf (registers || next_common || local.next_state)"
    unfolding conc_stmt_wf_def circuit_defs by auto
next
  show "nonneg_delay_conc (registers || next_common || local.next_state)"
    unfolding circuit_defs by auto
next
  show "conc_wt \<Gamma> (registers || next_common || local.next_state)"
    using cosine_locale_axioms by (auto intro!: conc_wt.intros)
next
   *)

                                                           
abbreviation is_posedge2 :: "'signal worldline_init \<Rightarrow> 'signal \<Rightarrow> nat \<Rightarrow>  bool" where
  "is_posedge2 w s j \<equiv> (snd w s (j - 1) = Bv False \<and> snd w s j = Bv True)"

fun next_signal :: "sig \<Rightarrow> sig" where
  "next_signal ACCUM        = NEXT_ACCUM" |
  "next_signal COUNTER      = NEXT_COUNTER" |
  "next_signal FRAC         = NEXT_FRAC" |
  "next_signal COMMON       = NEXT_COMMON" |
  "next_signal STATE        = NEXT_STATE" |
  "next_signal OUTREADY_REG = NEXT_OUTREADYREG"

abbreviation "bof_wline tw sig n \<equiv> bval_of (wline_of tw sig n)"
abbreviation "lof_wline tw sig n \<equiv> lval_of (wline_of tw sig n)"

fun zero_of :: "sig \<Rightarrow> val" where
  "zero_of ACCUM        = V_ZERO32" |
  "zero_of COUNTER      = V_ZERO3" |
  "zero_of FRAC         = V_ZERO32" |
  "zero_of COMMON       = V_ZERO32" |
  "zero_of STATE        = V_INIT" |
  "zero_of OUTREADY_REG = Bv False"

definition inv_reg :: "sig assn2" where
  "inv_reg tw \<equiv> (\<forall>s \<in> {ACCUM, COUNTER, FRAC, COMMON, STATE, OUTREADY_REG}. 
                 1 < fst tw \<longrightarrow> wline_of tw s (fst tw) = (if is_posedge2 (snd tw) CLK (fst tw - 1) then 
                                                            if bof_wline tw RST (fst tw - 1) then zero_of s else wline_of tw (next_signal s) (fst tw - 1) 
                                                          else wline_of tw s (fst tw - 1)))"

definition inv_reg2 :: "sig assn2" where
  "inv_reg2 tw \<equiv> disjnt {CLK} (event_of tw) \<or> wline_of tw CLK (fst tw) \<noteq> (Bv True) \<longrightarrow> 
                    (\<forall>i > fst tw. \<forall>s \<in> {ACCUM, COUNTER, FRAC, COMMON, STATE, OUTREADY_REG}. wline_of tw s i = wline_of tw s (fst tw))"

lemma snd_worldline_upd2:
  "sig \<noteq> sig' \<Longrightarrow> snd (snd (tw[sig, t :=\<^sub>2 v])) sig' t' = snd (snd tw) sig' t'"
  unfolding worldline_upd2_def worldline_upd_def by auto

lemma wp3_fun_trans_state:
  "wp3_fun \<Gamma> (Bassign_trans STATE S_INIT 1)
                            (\<lambda>tw. wityping \<Gamma> (snd tw) \<and>
                                  inv_reg (get_time tw + 1, snd tw[ OUTREADY_REG, 1 :=\<^sub>2 Bv False]) \<and>
                                  inv_reg2 (get_time tw + 1, snd tw[ OUTREADY_REG, 1 :=\<^sub>2 Bv False])) = 
                            (\<lambda>tw. wityping \<Gamma> (snd tw) 
                                  \<and> inv_reg  (get_time tw + 1, snd tw[ STATE, 1 :=\<^sub>2 V_INIT][ OUTREADY_REG, 1 :=\<^sub>2 Bv False]) 
                                  \<and> inv_reg2 (get_time tw + 1, snd tw[ STATE, 1 :=\<^sub>2 V_INIT][ OUTREADY_REG, 1 :=\<^sub>2 Bv False]))"
proof - 
  have "\<And>tw. type_of V_INIT = \<Gamma> STATE"
    using cosine_locale_axioms unfolding eval_world_raw.simps cosine_locale_def by (auto)
  hence *: "\<And>tw. wityping \<Gamma> (snd tw) \<Longrightarrow> wityping \<Gamma> (snd tw[ STATE, 1 :=\<^sub>2 V_INIT])"
    using worldline_upd_preserve_wityping
    by (simp add: worldline_upd_preserve_wityping worldline_upd2_def)  
  thus ?thesis
    unfolding wp3_fun.simps by auto
qed

lemma elim_wityping:
  assumes "type_of val = \<Gamma> sig"
  shows "(\<lambda>tw. wityping \<Gamma> (snd tw) \<and> wityping \<Gamma> (snd tw[ sig, t :=\<^sub>2 val]) \<and> Q tw) = 
         (\<lambda>tw. wityping \<Gamma> (snd tw) \<and> Q tw)"
proof -
  have "\<And>tw. wityping \<Gamma> (snd tw) \<Longrightarrow> wityping \<Gamma> (snd tw[ sig, t :=\<^sub>2 val])"
    using worldline_upd_preserve_wityping assms
    by (simp add: worldline_upd_preserve_wityping worldline_upd2_def)  
  thus ?thesis
    unfolding wp3_fun.simps by auto
qed

lemma type_of_common_frac:
  "type_of (Lv Sig U_ZERO32) = \<Gamma> COMMON"
  "type_of (Lv Sig U_ZERO32) = \<Gamma> FRAC"
  "type_of (Lv Sig U_ZERO32) = \<Gamma> ACCUM"
  using cosine_locale_axioms unfolding cosine_locale_def by auto

lemma type_of_counter_state:
  "type_of ( Lv Uns U_ZERO3) = \<Gamma> COUNTER"
  "type_of V_INIT = \<Gamma> STATE"
  using cosine_locale_axioms unfolding cosine_locale_def by auto

lemma elim_wityping_next:
  assumes "sig \<in> {ACCUM, COUNTER, FRAC, COMMON, STATE, OUTREADY_REG}"
  shows "(\<lambda>tw. wityping \<Gamma> (snd tw) \<and> wityping \<Gamma> (snd tw[ sig, t :=\<^sub>2 snd (snd tw) (next_signal sig) (fst tw)]) \<and> Q tw) = 
         (\<lambda>tw. wityping \<Gamma> (snd tw) \<and> Q tw)"
proof -
  have "\<And>tw. wityping \<Gamma> (snd tw) \<Longrightarrow> type_of (eval_world_raw2 tw (Bsig (next_signal sig))) = \<Gamma> sig"
    using cosine_locale_axioms unfolding eval_world_raw.simps cosine_locale_def wityping_def wtyping_def 
    using next_signal.simps assms by auto
  hence *: "\<And>tw. wityping \<Gamma> (snd tw) \<Longrightarrow> wityping \<Gamma> (snd tw[ sig, t :=\<^sub>2 eval_world_raw2 tw (Bsig (next_signal sig))])"
    using worldline_upd_preserve_wityping by (simp add: worldline_upd_preserve_wityping worldline_upd2_def) 
  thus ?thesis
    unfolding wp3_fun.simps fst_worldline_upd2 worldline_upd2_def by auto
qed

lemma state_in_set:
  "STATE \<in> {ACCUM, COUNTER, FRAC, COMMON, STATE, OUTREADY_REG}"
  by auto

lemma common_in_set:
  "COMMON \<in> {ACCUM, COUNTER, FRAC, COMMON, STATE, OUTREADY_REG}"
  by auto

lemma frac_in_set:
  "FRAC \<in> {ACCUM, COUNTER, FRAC, COMMON, STATE, OUTREADY_REG}"
  by auto

lemma counter_in_set:
  "COUNTER \<in> {ACCUM, COUNTER, FRAC, COMMON, STATE, OUTREADY_REG}"
  by auto

lemma accum_in_set:
  "ACCUM \<in> {ACCUM, COUNTER, FRAC, COMMON, STATE, OUTREADY_REG}"
  by auto

lemma inv_reg2_next_time_rst:
  fixes tw v
  defines "tw' \<equiv> tw[ ACCUM, 1 :=\<^sub>2 V_ZERO32][ COUNTER, 1 :=\<^sub>2 V_ZERO3][ FRAC, 1 :=\<^sub>2 V_ZERO32][ COMMON, 1 :=\<^sub>2 V_ZERO32][ STATE, 1 :=\<^sub>2 V_INIT][ OUTREADY_REG, 1 :=\<^sub>2 Bv False]"
  shows   "inv_reg2 (fst tw' + 1, snd tw')"
  unfolding inv_reg2_def 
proof (intro impI, rule allI, rule impI, rule ballI)
  fix i s
  have "fst tw' = fst tw"
    unfolding tw'_def fst_worldline_upd2 by auto
  assume "get_time (get_time tw' + 1, snd tw') < i"
  hence "fst tw + 1 < i"
    unfolding `fst tw' = fst tw` by auto
  assume "s \<in> {ACCUM, COUNTER, FRAC, COMMON, STATE, OUTREADY_REG}"
  have * : " wline_of (get_time tw' + 1, snd tw') s (get_time (get_time tw' + 1, snd tw')) = wline_of (fst tw + 1, snd tw') s (fst tw + 1)"
    unfolding `fst tw' = fst tw` by auto

  have "s \<in> {ACCUM, FRAC, COMMON} \<or> s = COUNTER \<or> s = STATE \<or> s = OUTREADY_REG"
    using `s \<in> {ACCUM, COUNTER, FRAC, COMMON, STATE, OUTREADY_REG}` by auto
  moreover
  { assume "s \<in> {ACCUM, FRAC, COMMON} "
    hence "wline_of (fst tw + 1, snd tw') s (fst tw + 1) = V_ZERO32"
      unfolding tw'_def worldline_upd2_def worldline_upd_def by auto
    also have "... = wline_of (fst tw + 1, snd tw') s i"
      using `s \<in> {ACCUM, FRAC, COMMON}` 
      using `fst tw + 1 < i` unfolding tw'_def worldline_upd2_def worldline_upd_def  by auto
    finally have "wline_of (fst tw + 1, snd tw') s (fst tw + 1) = wline_of (fst tw + 1, snd tw') s i"
      by auto }
  moreover
  { assume "s = COUNTER"
    hence "wline_of (fst tw + 1, snd tw') s (fst tw + 1) = V_ZERO3"
      unfolding tw'_def worldline_upd2_def worldline_upd_def by auto
    also have "... = wline_of (fst tw + 1, snd tw') s i"
      using `s = COUNTER` `fst tw + 1 < i` unfolding tw'_def worldline_upd2_def worldline_upd_def  
      by auto
    finally have "wline_of (fst tw + 1, snd tw') s (fst tw + 1) = wline_of (fst tw + 1, snd tw') s i"
      by auto }
  moreover
  { assume "s = STATE"
    hence "wline_of (fst tw + 1, snd tw') s (fst tw + 1) = V_INIT"
      unfolding tw'_def worldline_upd2_def worldline_upd_def by auto
    also have "... = wline_of (fst tw + 1, snd tw') s i"
      using `s = STATE` `fst tw + 1 < i` unfolding tw'_def worldline_upd2_def worldline_upd_def  
      by auto
    finally have "wline_of (fst tw + 1, snd tw') s (fst tw + 1) = wline_of (fst tw + 1, snd tw') s i"
      by auto }
  moreover
  { assume "s = OUTREADY_REG"
    hence "wline_of (fst tw + 1, snd tw') s (fst tw + 1) = Bv False"
      unfolding tw'_def worldline_upd2_def worldline_upd_def by auto
    also have "... = wline_of (fst tw + 1, snd tw') s i"
      using `s = OUTREADY_REG` `fst tw + 1 < i` unfolding tw'_def worldline_upd2_def worldline_upd_def  
      by auto
    finally have "wline_of (fst tw + 1, snd tw') s (fst tw + 1) = wline_of (fst tw + 1, snd tw') s i"
      by auto }
  ultimately have "wline_of (fst tw + 1, snd tw') s (fst tw + 1) = wline_of (fst tw + 1, snd tw') s i"
    by auto
  with * show "wline_of (get_time tw' + 1, snd tw') s i = wline_of (get_time tw' + 1, snd tw') s (get_time (get_time tw' + 1, snd tw'))"
    by auto
qed

lemma inv_reg_next_time_rst:
  fixes tw
  assumes "eval_world_raw2 tw (Bsig RST) = Bv True"
  defines "tw' \<equiv> tw[ ACCUM, 1 :=\<^sub>2 V_ZERO32][ COUNTER, 1 :=\<^sub>2 V_ZERO3][ FRAC, 1 :=\<^sub>2 V_ZERO32][ COMMON, 1 :=\<^sub>2 V_ZERO32][ STATE, 1 :=\<^sub>2 V_INIT][ OUTREADY_REG, 1 :=\<^sub>2 Bv False]"
  assumes "\<not> disjnt {CLK} (event_of tw)"
  assumes "eval_world_raw2 tw (Bsig CLK) = Bv True"
  assumes "wityping \<Gamma> (snd tw)"
  shows   "inv_reg (fst tw' + 1, snd tw')"
  unfolding inv_reg_def
proof (rule ballI, rule impI)
  fix s
  assume "s \<in> {ACCUM, COUNTER, FRAC, COMMON, STATE, OUTREADY_REG}"
  have "fst tw'  = fst tw"
    unfolding tw'_def by auto
  have "bval_of (wline_of (get_time tw' + 1, snd tw') RST (get_time (get_time tw' + 1, snd tw') - 1))"
    using assms(1) unfolding eval_world_raw.simps `fst tw' = fst tw` tw'_def 
    worldline_upd2_def worldline_upd_def by auto
  hence "bof_wline (fst tw' + 1, snd tw') RST (fst tw')"
    by auto
  assume "1 < get_time (get_time tw' + 1, snd tw')"
  hence "0 < fst tw" 
    unfolding tw'_def worldline_upd2_def worldline_upd_def by auto
  have *: "wline_of tw CLK (fst tw) \<noteq> wline_of tw CLK (fst tw - 1)"
    using assms(3) `0 < fst tw` unfolding event_of_alt_def by auto
  have **: "wline_of tw CLK (fst tw) = Bv True"
    using assms(4) by auto
  hence "wline_of tw CLK (fst tw - 1) = Bv False"
    using *  by (smt assms(5) comp_apply ty.distinct(1) type_of.elims type_of.simps(1) wityping_def wtyping_def)
  hence prev_false: "snd (snd (get_time tw' + 1, snd tw')) CLK (get_time (get_time tw' + 1, snd tw') - 1 - 1) = Bv False"
    unfolding snd_conv fst_conv tw'_def worldline_upd2_def worldline_upd_def by auto
  have curr_true : "snd (snd (get_time tw' + 1, snd tw')) CLK (get_time (get_time tw' + 1, snd tw') - 1) = Bv True"
    using ** unfolding snd_conv fst_conv `fst tw' = fst tw` tw'_def worldline_upd2_def worldline_upd_def by auto
  hence "is_posedge2 (snd tw') CLK (fst tw')"
    using prev_false by auto
  have "wline_of (get_time tw' + 1, snd tw') s (get_time (get_time tw' + 1, snd tw')) = wline_of (fst tw + 1, snd tw') s (fst tw + 1)"
    unfolding `fst tw' = fst tw` by auto
  also have "... = zero_of s"
    using zero_of.simps `s \<in> {ACCUM, COUNTER, FRAC, COMMON, STATE, OUTREADY_REG}`
    unfolding tw'_def  worldline_upd2_def worldline_upd_def by auto
  finally show "wline_of (get_time tw' + 1, snd tw') s (get_time (get_time tw' + 1, snd tw')) =
         (if snd (snd (get_time tw' + 1, snd tw')) CLK (get_time (get_time tw' + 1, snd tw') - 1 - 1) = Bv False \<and>
             snd (snd (get_time tw' + 1, snd tw')) CLK (get_time (get_time tw' + 1, snd tw') - 1) = Bv True
          then if bval_of (wline_of (get_time tw' + 1, snd tw') RST (get_time (get_time tw' + 1, snd tw') - 1)) then zero_of s
               else wline_of (get_time tw' + 1, snd tw') (next_signal s) (get_time (get_time tw' + 1, snd tw') - 1)
          else wline_of (get_time tw' + 1, snd tw') s (get_time (get_time tw' + 1, snd tw') - 1))"
    using `bof_wline (fst tw' + 1, snd tw') RST (fst tw')` `is_posedge2 (snd tw') CLK (fst tw')` 
    unfolding snd_conv fst_conv by auto
qed

lemma inv_reg_next_time_clk:
  fixes tw
  assumes "\<not> disjnt {CLK} (event_of tw)"
  assumes "eval_world_raw2 tw (Bsig RST) \<noteq> Bv True"
  assumes "eval_world_raw2 tw (Bsig CLK) = Bv True"
  defines "tw' \<equiv> tw[ ACCUM, 1 :=\<^sub>2 snd (snd tw) NEXT_ACCUM (fst tw)]
                   [ COUNTER, 1 :=\<^sub>2 snd (snd tw) NEXT_COUNTER (fst tw)]
                   [ FRAC, 1 :=\<^sub>2 snd (snd tw) NEXT_FRAC (fst tw)]
                   [ COMMON, 1 :=\<^sub>2 snd (snd tw) NEXT_COMMON (fst tw)]
                   [ STATE, 1 :=\<^sub>2 snd (snd tw) NEXT_STATE (fst tw)]
                   [ OUTREADY_REG, 1 :=\<^sub>2 snd (snd tw) NEXT_OUTREADYREG (fst tw)]"
  assumes "wityping \<Gamma> (snd tw)"
  assumes "inv_reg tw"
  shows   "inv_reg (fst tw' + 1, snd tw')"
  unfolding inv_reg_def
proof (rule, rule)
  have tw'_alt_def: "tw' = tw[ ACCUM, 1 :=\<^sub>2 snd (snd tw) (next_signal ACCUM) (fst tw)]
                             [ COUNTER, 1 :=\<^sub>2 snd (snd tw) (next_signal COUNTER) (fst tw)]
                             [ FRAC, 1 :=\<^sub>2 snd (snd tw) (next_signal FRAC) (fst tw)]
                             [ COMMON, 1 :=\<^sub>2 snd (snd tw) (next_signal COMMON) (fst tw)]
                             [ STATE, 1 :=\<^sub>2 snd (snd tw) (next_signal STATE) (fst tw)]
                             [ OUTREADY_REG, 1 :=\<^sub>2 snd (snd tw) (next_signal OUTREADY_REG) (fst tw)]"
    unfolding tw'_def next_signal.simps by auto
  have "fst tw' = fst tw"
    unfolding tw'_def worldline_upd2_def worldline_upd_def by auto
  have "\<Gamma> RST = Bty"
    using cosine_locale_axioms unfolding cosine_locale_def by auto
  hence "type_of (snd (snd tw) RST (fst tw)) = Bty" 
    using assms(5) unfolding wityping_def wtyping_def by auto
  hence "snd (snd tw) RST (get_time tw) = Bv False"
    using assms(2) assms(5) unfolding eval_world_raw.simps  by (metis ty.distinct(1) type_of.elims)
  hence not_bval: "\<not> bval_of (wline_of (get_time tw' + 1, snd tw') RST (get_time (get_time tw' + 1, snd tw') - 1))"
    unfolding `fst tw' = fst tw` tw'_def fst_conv worldline_upd2_def worldline_upd_def by auto 
  assume "1 < get_time (get_time tw' + 1, snd tw')"
  hence "0 < fst tw" 
    unfolding tw'_def worldline_upd2_def worldline_upd_def by auto
  have *: "wline_of tw CLK (fst tw) \<noteq> wline_of tw CLK (fst tw - 1)"
    using assms(1) `0 < fst tw` unfolding event_of_alt_def by auto
  have **: "wline_of tw CLK (fst tw) = Bv True"
    using assms(3) by auto
  hence "wline_of tw CLK (fst tw - 1) = Bv False"
    using *  by (smt assms(5) comp_apply ty.distinct(1) type_of.elims type_of.simps(1) wityping_def wtyping_def)
  hence prev_false: "snd (snd (get_time tw' + 1, snd tw')) CLK (get_time (get_time tw' + 1, snd tw') - 1 - 1) = Bv False"
    unfolding snd_conv fst_conv tw'_def worldline_upd2_def worldline_upd_def by auto
  have curr_true : "snd (snd (get_time tw' + 1, snd tw')) CLK (get_time (get_time tw' + 1, snd tw') - 1) = Bv True"
    using ** unfolding snd_conv fst_conv `fst tw' = fst tw` tw'_def worldline_upd2_def worldline_upd_def by auto
  fix s 
  assume s_set: " s \<in> {ACCUM, COUNTER, FRAC, COMMON, STATE, OUTREADY_REG}"
  have " wline_of (get_time tw' + 1, snd tw') s (get_time (get_time tw' + 1, snd tw')) = wline_of (fst tw + 1, snd tw') s (fst tw + 1)"
    unfolding `fst tw' = fst tw` by auto
  also have "... = (snd (snd tw) (next_signal s) (fst tw))"
    using s_set unfolding tw'_alt_def worldline_upd2_def worldline_upd_def by auto
  also have "... = wline_of (get_time tw' + 1, snd tw') (next_signal s) (get_time (get_time tw' + 1, snd tw') - 1)"
    unfolding `fst tw' = fst tw` fst_conv tw'_alt_def worldline_upd2_def worldline_upd_def by auto 
  finally show "         wline_of (get_time tw' + 1, snd tw') s (get_time (get_time tw' + 1, snd tw')) =
         (if snd (snd (get_time tw' + 1, snd tw')) CLK (get_time (get_time tw' + 1, snd tw') - 1 - 1) = Bv False \<and>
             snd (snd (get_time tw' + 1, snd tw')) CLK (get_time (get_time tw' + 1, snd tw') - 1) = Bv True
          then if bval_of (wline_of (get_time tw' + 1, snd tw') RST (get_time (get_time tw' + 1, snd tw') - 1)) then zero_of s
               else wline_of (get_time tw' + 1, snd tw') (next_signal s) (get_time (get_time tw' + 1, snd tw') - 1)
          else wline_of (get_time tw' + 1, snd tw') s (get_time (get_time tw' + 1, snd tw') - 1))"
    using prev_false curr_true not_bval by auto
qed

lemma inv_reg2_next_time_clk:
  fixes tw
  defines "tw' \<equiv> tw[ ACCUM, 1 :=\<^sub>2 snd (snd tw) NEXT_ACCUM (fst tw)]
                   [ COUNTER, 1 :=\<^sub>2 snd (snd tw) NEXT_COUNTER (fst tw)]
                   [ FRAC, 1 :=\<^sub>2 snd (snd tw) NEXT_FRAC (fst tw)]
                   [ COMMON, 1 :=\<^sub>2 snd (snd tw) NEXT_COMMON (fst tw)]
                   [ STATE, 1 :=\<^sub>2 snd (snd tw) NEXT_STATE (fst tw)]
                   [ OUTREADY_REG, 1 :=\<^sub>2 snd (snd tw) NEXT_OUTREADYREG (fst tw)]"
  shows   "inv_reg2 (fst tw' + 1, snd tw')"
  unfolding inv_reg2_def
proof (rule, rule, rule, rule, unfold fst_conv)
  have tw'_alt_def: "tw' = tw[ ACCUM, 1 :=\<^sub>2 snd (snd tw) (next_signal ACCUM) (fst tw)]
                             [ COUNTER, 1 :=\<^sub>2 snd (snd tw) (next_signal COUNTER) (fst tw)]
                             [ FRAC, 1 :=\<^sub>2 snd (snd tw) (next_signal FRAC) (fst tw)]
                             [ COMMON, 1 :=\<^sub>2 snd (snd tw) (next_signal COMMON) (fst tw)]
                             [ STATE, 1 :=\<^sub>2 snd (snd tw) (next_signal STATE) (fst tw)]
                             [ OUTREADY_REG, 1 :=\<^sub>2 snd (snd tw) (next_signal OUTREADY_REG) (fst tw)]"
    unfolding tw'_def next_signal.simps by auto
  fix i s
  assume "s \<in> {ACCUM, COUNTER, FRAC, COMMON, STATE, OUTREADY_REG}"
  have "fst tw' = fst tw"
    unfolding tw'_def worldline_upd2_def worldline_upd_def by auto
  assume "fst tw' + 1 < i"
  hence "fst tw + 1 < i"
    unfolding `fst tw' = fst tw` by auto
  have " wline_of (get_time tw' + 1, snd tw') s i = snd (snd tw) (next_signal s) (fst tw)"
    using `s \<in> {ACCUM, COUNTER, FRAC, COMMON, STATE, OUTREADY_REG}` `fst tw + 1 < i`
    unfolding tw'_alt_def worldline_upd2_def worldline_upd_def by auto
  also have "... = wline_of (get_time tw' + 1, snd tw') s (get_time tw' + 1)"
    using `s \<in> {ACCUM, COUNTER, FRAC, COMMON, STATE, OUTREADY_REG}` `fst tw + 1 < i`
    unfolding `fst tw' = fst tw` tw'_alt_def worldline_upd2_def worldline_upd_def by auto
  finally show " wline_of (get_time tw' + 1, snd tw') s i = wline_of (get_time tw' + 1, snd tw') s (get_time tw' + 1)"
    by auto
qed

lemma inv_reg_preserved:
  "\<And>tw. inv_reg tw \<and> inv_reg2 tw \<and> (disjnt {CLK} (event_of tw) \<or> wline_of tw CLK (fst tw) \<noteq> (Bv True)) \<Longrightarrow> inv_reg (fst tw + 1, snd tw)"
proof -
  fix tw
  assume "inv_reg tw \<and> inv_reg2 tw \<and> (disjnt {CLK} (event_of tw) \<or> wline_of tw CLK (fst tw) \<noteq> (Bv True))"
  hence "inv_reg tw" "inv_reg2 tw" and *: "(disjnt {CLK} (event_of tw) \<or> wline_of tw CLK (fst tw) \<noteq> (Bv True))"
    by auto
  { fix s
    assume s_set: "s \<in> {ACCUM, COUNTER, FRAC, COMMON, STATE, OUTREADY_REG}"
    assume "0 < fst tw"
    hence "\<not> is_posedge2 (snd tw) CLK (fst tw)"
      using * unfolding event_of_alt_def by auto
    have **: " wline_of tw s (fst tw + 1) = wline_of tw s (fst tw)"
      using `inv_reg2 tw` * s_set unfolding inv_reg2_def by auto
    hence "wline_of tw s (fst tw + 1) = (if is_posedge2 (snd tw) CLK (fst tw) then 
                                            if bof_wline tw RST (fst tw) then zero_of s  else wline_of tw (next_signal s) (fst tw) 
                                         else wline_of tw s (fst tw))"
      using `\<not> is_posedge2 (snd tw) CLK (fst tw)` by auto }
  thus "inv_reg (fst tw + 1, snd tw)"
    unfolding inv_reg_def comp_def fst_conv snd_conv by auto
qed

lemma inv_reg2_preserved:
  "\<And>tw. inv_reg2 tw \<and> (disjnt {CLK} (event_of tw) \<or> wline_of tw CLK (fst tw) \<noteq> (Bv True)) \<Longrightarrow> inv_reg2 (fst tw + 1, snd tw)"
  unfolding inv_reg2_def by auto

lemma correctness_registers:
  "\<Gamma> \<turnstile>\<^sub>s \<lbrace>\<lambda>tw. inv_reg tw \<and> inv_reg2 tw\<rbrace> registers \<lbrace>\<lambda>tw. inv_reg tw \<and> inv_reg2 tw\<rbrace>"
  apply (rule While_Suc)
  apply (rule Conseq'[where P="wp3_conc \<Gamma> registers (\<lambda>tw. inv_reg  (fst tw + 1, snd tw) \<and> 
                                                          inv_reg2 (fst tw + 1, snd tw))", rotated])
  apply (rule wp3_conc_is_pre, rule conc_stmt_wf_registers, rule nonneg_delay_conc_registers, rule cwt_reg, simp)
  unfolding registers_def wp3_conc_single'[OF cwt_reg[unfolded registers_def] nonneg_delay_conc_registers[unfolded registers_def]]
  wp3_fun.simps(7) wp3_fun.simps(8)
  wp3_fun.simps(2)[of _ "OUTREADY_REG"] fst_worldline_upd2 eval_world_raw.simps 
  wp3_fun.simps(2)[of _ "STATE"] elim_wityping[OF type_of_counter_state(2)] elim_wityping_next[OF state_in_set, unfolded next_signal.simps] snd_worldline_upd2[OF sig.simps(224)]
  wp3_fun.simps(2)[of _ "COMMON"] elim_wityping[OF type_of_common_frac(1)]  elim_wityping_next[OF common_in_set, unfolded next_signal.simps] 
      snd_worldline_upd2[OF sig.simps(407)] snd_worldline_upd2[OF sig.simps(214)]
  wp3_fun.simps(2)[of _ "FRAC"] elim_wityping[OF type_of_common_frac(2)] elim_wityping_next[OF frac_in_set, unfolded next_signal.simps] 
      snd_worldline_upd2[OF sig.simps(355)] snd_worldline_upd2[OF sig.simps(365)] snd_worldline_upd2[OF sig.simps(210)]
  wp3_fun.simps(2)[of _ "COUNTER"] elim_wityping[OF type_of_counter_state(1)] elim_wityping_next[OF counter_in_set, unfolded next_signal.simps]
      snd_worldline_upd2[OF sig.simps(301)] snd_worldline_upd2[OF sig.simps(305)] snd_worldline_upd2[OF sig.simps(315)] snd_worldline_upd2[OF sig.simps(206)]
  wp3_fun.simps(2)[of _ "ACCUM"] elim_wityping [OF type_of_common_frac(3)] elim_wityping_next[OF accum_in_set, unfolded next_signal.simps]
      snd_worldline_upd2[OF sig.simps(239)] snd_worldline_upd2[OF sig.simps(243)] snd_worldline_upd2[OF sig.simps(247)] snd_worldline_upd2[OF sig.simps(257)] snd_worldline_upd2[OF sig.simps(202)]
  wp3_fun.simps(1)
proof (rule, rule, unfold if_bool_eq_conj, rule, rule_tac[!] impI, rule_tac[2] conjI, rule_tac[2] impI, rule_tac[2] conjI, rule_tac[2] impI, rule_tac[3] impI, rule_tac[4] impI)
  fix w 
  assume "wityping \<Gamma> (snd w) \<and> inv_reg w \<and> inv_reg2 w" and "disjnt {CLK} (event_of w)"
  thus "(inv_reg (get_time w + 1, snd w) \<and> inv_reg2 (get_time w + 1, snd w)) \<and> wityping \<Gamma> (snd w)"
    using inv_reg_preserved inv_reg2_preserved by auto
next
  fix w
  assume "wityping \<Gamma> (snd w) \<and> inv_reg w \<and> inv_reg2 w"
  hence tyclk: "type_of (snd (snd w) CLK (get_time w)) = Bty"
    using cosine_locale_axioms unfolding cosine_locale_def wityping_def wtyping_def by auto
  assume "eval_logical (snd (snd w) CLK (get_time w)) (Bv (CLK \<in> event_of (get_time w, snd w))) (\<and>) = Bv True"
  hence eval: "eval_world_raw2 w (Bsig CLK) = Bv True"
    using tyclk by (auto split: val.splits)
  assume "snd (snd w) RST (get_time w) = Bv True"
     and "wityping \<Gamma> (snd w) \<and> inv_reg w \<and> inv_reg2 w"
     and " \<not> disjnt {CLK} (event_of w)" 
  thus " wityping \<Gamma> (snd w) \<and>
         inv_reg
          (get_time w + 1,
           snd w[ ACCUM, 1 :=\<^sub>2 V_ZERO32][ COUNTER, 1 :=\<^sub>2 V_ZERO3][ FRAC, 1 :=\<^sub>2 V_ZERO32][ COMMON, 1 :=\<^sub>2 V_ZERO32][ STATE, 1 :=\<^sub>2 V_INIT][ OUTREADY_REG, 1 :=\<^sub>2 Bv False]) \<and>
         inv_reg2
          (get_time w + 1,
           snd w[ ACCUM, 1 :=\<^sub>2 V_ZERO32][ COUNTER, 1 :=\<^sub>2 V_ZERO3][ FRAC, 1 :=\<^sub>2 V_ZERO32][ COMMON, 1 :=\<^sub>2 V_ZERO32][ STATE, 1 :=\<^sub>2 V_INIT][ OUTREADY_REG, 1 :=\<^sub>2 Bv False])"
    using eval inv_reg2_next_time_rst inv_reg_next_time_rst by auto
next
  fix w
  assume wt: "wityping \<Gamma> (snd w) \<and> inv_reg w \<and> inv_reg2 w"
  hence tyclk: "type_of (snd (snd w) CLK (get_time w)) = Bty"
    using cosine_locale_axioms unfolding cosine_locale_def wityping_def wtyping_def by auto
  assume "eval_logical (snd (snd w) CLK (get_time w)) (Bv (CLK \<in> event_of (get_time w, snd w))) (\<and>) = Bv True"
  hence eval: "eval_world_raw2 w (Bsig CLK) = Bv True"
    using tyclk by (auto split: val.splits)
  assume "\<not> disjnt {CLK} (event_of w)"
     and "snd (snd w) RST (get_time w) \<noteq> Bv True"
  thus "wityping \<Gamma> (snd w) \<and>
         inv_reg
          (get_time w + 1,
           snd w[ ACCUM, 1 :=\<^sub>2 snd (snd w) NEXT_ACCUM
                                 (get_time
                                   w)][ COUNTER, 1 :=\<^sub>2 snd (snd w) NEXT_COUNTER
                                                         (get_time
                                                           w)][ FRAC, 1 :=\<^sub>2 snd (snd w) NEXT_FRAC
                                                                              (get_time
                                                                                w)][ COMMON, 1 :=\<^sub>2 snd (snd w) NEXT_COMMON
       (get_time w)][ STATE, 1 :=\<^sub>2 snd (snd w) NEXT_STATE (get_time w)][ OUTREADY_REG, 1 :=\<^sub>2 snd (snd w) NEXT_OUTREADYREG (get_time w)]) \<and>
         inv_reg2
          (get_time w + 1,
           snd w[ ACCUM, 1 :=\<^sub>2 snd (snd w) NEXT_ACCUM
                                 (get_time
                                   w)][ COUNTER, 1 :=\<^sub>2 snd (snd w) NEXT_COUNTER
                                                         (get_time
                                                           w)][ FRAC, 1 :=\<^sub>2 snd (snd w) NEXT_FRAC
                                                                              (get_time
                                                                                w)][ COMMON, 1 :=\<^sub>2 snd (snd w) NEXT_COMMON
       (get_time w)][ STATE, 1 :=\<^sub>2 snd (snd w) NEXT_STATE (get_time w)][ OUTREADY_REG, 1 :=\<^sub>2 snd (snd w) NEXT_OUTREADYREG (get_time w)])"
    using wt eval inv_reg_next_time_clk inv_reg2_next_time_clk unfolding eval_world_raw.simps
    by auto
next
  fix w 
  assume wt: "wityping \<Gamma> (snd w) \<and> inv_reg w \<and> inv_reg2 w" and "\<not> disjnt {CLK} (event_of w)"
    and " eval_logical (snd (snd w) CLK (get_time w)) (Bv (CLK \<in> event_of (get_time w, snd w))) (\<and>) \<noteq> Bv True"
  hence "wline_of w CLK (get_time w) \<noteq> Bv True"
    by (auto split:val.splits)
  thus "(inv_reg (get_time w + 1, snd w) \<and> inv_reg2 (get_time w + 1, snd w)) \<and> wityping \<Gamma> (snd w)"
    using wt inv_reg_preserved inv_reg2_preserved by auto
qed

section \<open>Functional specification of @{term "next_state"}\<close>

definition inv_nstate :: "sig assn2" where
  "inv_nstate tw = (wline_of tw NEXT_STATE (fst tw) = 
                   (case wline_of tw STATE (fst tw - 1) of 
                      V_INIT \<Rightarrow> V_WAIT | 
                      V_WAIT \<Rightarrow> (if bof_wline tw INREADY (fst tw - 1) then V_PRE else V_WAIT) |
                      V_PRE  \<Rightarrow> V_PROC  |
                      V_PROC \<Rightarrow> (if bof_wline tw CTR_NEQ_0 (fst tw - 1) then V_PROC else V_POST) |
                      V_POST \<Rightarrow> V_WAIT |
                      _      \<Rightarrow> V_INIT
                   ))"

definition inv_nstate2 :: "sig assn2" where
  "inv_nstate2 tw \<equiv> disjnt {STATE, INREADY, CTR_NEQ_0} (event_of tw) \<longrightarrow> 
                          (\<forall>i > fst tw. wline_of tw NEXT_STATE i = wline_of tw NEXT_STATE (fst tw))"

lemma inv_nstate2_preserved:
  "\<And>tw. inv_nstate2 tw \<and> (disjnt {STATE, INREADY, CTR_NEQ_0} (event_of tw)) \<Longrightarrow> inv_nstate2 (fst tw + 1, snd tw)"
  unfolding inv_nstate2_def by auto

lemma inv_nstate_preserved:
  "\<And>tw. inv_nstate tw \<and> inv_nstate2 tw \<and>  (disjnt {STATE, INREADY, CTR_NEQ_0} (event_of tw)) \<Longrightarrow> inv_nstate (fst tw + 1, snd tw)"
proof -
  fix tw
  assume "inv_nstate tw \<and> inv_nstate2 tw \<and> (disjnt {STATE, INREADY, CTR_NEQ_0} (event_of tw))"
  hence "inv_nstate tw" "inv_nstate2 tw" and *: "(disjnt {STATE, INREADY, CTR_NEQ_0} (event_of tw))"
    by auto
  have eq0: "wline_of tw STATE (fst tw) = wline_of tw STATE (fst tw - 1)" and 
       eq1: "wline_of tw INREADY (fst tw) = wline_of tw INREADY (fst tw - 1)" and 
       eq2: "wline_of tw CTR_NEQ_0 (fst tw) = wline_of tw CTR_NEQ_0 (fst tw - 1)"
    using * unfolding event_of_alt_def by (smt diff_0_eq_0 disjnt_insert1 mem_Collect_eq)+
  have "wline_of tw NEXT_STATE (fst tw + 1) = wline_of tw NEXT_STATE (fst tw)"
    using `inv_nstate2 tw` * unfolding inv_nstate2_def  by (simp add: next_time_world_at_least) 
  also have "... = (case wline_of tw STATE (fst tw - 1) of 
                      V_INIT \<Rightarrow> V_WAIT | 
                      V_WAIT \<Rightarrow> (if bof_wline tw INREADY (fst tw - 1) then V_PRE else V_WAIT) |
                      V_PRE  \<Rightarrow> V_PROC  |
                      V_PROC \<Rightarrow> (if bof_wline tw CTR_NEQ_0 (fst tw - 1) then V_PROC else V_POST) |
                      V_POST \<Rightarrow> V_WAIT |
                      _      \<Rightarrow> V_INIT)"
    using `inv_nstate tw` unfolding inv_nstate_def by auto
  also have "... = (case wline_of tw STATE (fst tw) of 
                      V_INIT \<Rightarrow> V_WAIT | 
                      V_WAIT \<Rightarrow> (if bof_wline tw INREADY (fst tw) then V_PRE else V_WAIT) |
                      V_PRE  \<Rightarrow> V_PROC  |
                      V_PROC \<Rightarrow> (if bof_wline tw CTR_NEQ_0 (fst tw) then V_PROC else V_POST) |
                      V_POST \<Rightarrow> V_WAIT |
                      _      \<Rightarrow> V_INIT)"
    unfolding eq0 eq1 eq2 by auto
  finally show "inv_nstate (fst tw + 1, snd tw)"
    unfolding inv_nstate_def by auto  
qed

lemma inv_nstate2: 
  fixes tw v
  defines "tw' \<equiv> tw[NEXT_STATE, 1 :=\<^sub>2 v]"
  shows   "inv_nstate2 (fst tw' + 1, snd tw')"
  unfolding inv_nstate2_def tw'_def worldline_upd2_def worldline_upd_def by auto

lemma inv_nstate_vinit:
  fixes tw
  assumes " snd (snd tw) STATE (fst tw) = V_INIT"
  defines "tw' \<equiv> tw[ NEXT_STATE, 1 :=\<^sub>2 V_WAIT]"
  shows   "inv_nstate (fst tw' + 1, snd tw')"
proof -
  have "fst tw' = fst tw"
    unfolding tw'_def worldline_upd2_def worldline_upd_def by auto
  have "wline_of tw' NEXT_STATE (fst tw + 1) = V_WAIT"
    unfolding tw'_def worldline_upd2_def worldline_upd_def by auto
  moreover have "wline_of (get_time tw' + 1, snd tw') STATE (get_time (get_time tw' + 1, snd tw') - 1) = V_INIT"
    using assms(2) snd_worldline_upd2 unfolding fst_conv `fst tw' = fst tw` comp_def snd_conv 
    by (simp add: snd_worldline_upd2 assms(1))
  ultimately show ?thesis
    unfolding inv_nstate_def `fst tw' = fst tw` by auto
qed

lemma inv_nstate_vwait_true:
  fixes tw
  assumes " snd (snd tw) STATE (fst tw) = V_WAIT"
  assumes " snd (snd tw) INREADY (get_time tw) = Bv True"
  defines "tw' \<equiv> tw[ NEXT_STATE, 1 :=\<^sub>2 V_PRE]"
  shows   "inv_nstate (fst tw' + 1, snd tw')"
proof -
  have "fst tw' = fst tw"
    unfolding tw'_def worldline_upd2_def worldline_upd_def by auto
  have "wline_of tw' NEXT_STATE (fst tw + 1) = V_PRE"
    unfolding tw'_def worldline_upd2_def worldline_upd_def by auto
  moreover have "wline_of (get_time tw' + 1, snd tw') STATE (get_time (get_time tw' + 1, snd tw') - 1) = V_WAIT"
    using assms(2) snd_worldline_upd2 unfolding fst_conv `fst tw' = fst tw` comp_def snd_conv 
    by (simp add: snd_worldline_upd2 assms(1) tw'_def)
  ultimately show ?thesis
    using assms(2) snd_worldline_upd2[OF sig.simps(118)] unfolding inv_nstate_def `fst tw' = fst tw`  tw'_def 
    by auto
qed

lemma inv_nstate_vwait_false:
  fixes tw
  assumes " snd (snd tw) STATE (fst tw) = V_WAIT"
  assumes " snd (snd tw) INREADY (get_time tw) \<noteq>  Bv True"
  defines "tw' \<equiv> tw[ NEXT_STATE, 1 :=\<^sub>2 V_WAIT]"
  assumes "wityping \<Gamma> (snd tw)"
  shows   "inv_nstate (fst tw' + 1, snd tw')"
proof -
  have assms2: "snd (snd tw) INREADY (fst tw) = Bv False"
    using `wityping \<Gamma> (snd tw)` 
    by (smt assms(2) cosine_locale_axioms cosine_locale_def ty.distinct(1) type_of.elims val.inject(1) wityping_def wtyping_def)
  have "fst tw' = fst tw"
    unfolding tw'_def worldline_upd2_def worldline_upd_def by auto
  have "wline_of tw' NEXT_STATE (fst tw + 1) = V_WAIT"
    unfolding tw'_def worldline_upd2_def worldline_upd_def by auto
  moreover have "wline_of (get_time tw' + 1, snd tw') STATE (get_time (get_time tw' + 1, snd tw') - 1) = V_WAIT"
    using assms(2) snd_worldline_upd2 unfolding fst_conv `fst tw' = fst tw` comp_def snd_conv 
    by (simp add: snd_worldline_upd2 assms(1) tw'_def)
  ultimately show ?thesis
    using assms2 snd_worldline_upd2[OF sig.simps(118)] unfolding inv_nstate_def `fst tw' = fst tw`  tw'_def 
    by auto
qed

lemma inv_nstate_vpre:
  fixes tw
  assumes " snd (snd tw) STATE (fst tw) = V_PRE"
  defines "tw' \<equiv> tw[ NEXT_STATE, 1 :=\<^sub>2 V_PROC]"
  shows   "inv_nstate (fst tw' + 1, snd tw')"
proof -
  have "fst tw' = fst tw"
    unfolding tw'_def worldline_upd2_def worldline_upd_def by auto
  have "wline_of tw' NEXT_STATE (fst tw + 1) = V_PROC"
    unfolding tw'_def worldline_upd2_def worldline_upd_def by auto
  moreover have "wline_of (get_time tw' + 1, snd tw') STATE (get_time (get_time tw' + 1, snd tw') - 1) = V_PRE"
    using assms(2) snd_worldline_upd2 unfolding fst_conv `fst tw' = fst tw` comp_def snd_conv 
    by (simp add: snd_worldline_upd2 assms(1))
  ultimately show ?thesis
    unfolding inv_nstate_def `fst tw' = fst tw` by auto
qed

lemma inv_nstate_vproc_true:
  fixes tw
  assumes " snd (snd tw) STATE (fst tw) = V_PROC"
  assumes " snd (snd tw) CTR_NEQ_0 (get_time tw) = Bv True"
  defines "tw' \<equiv> tw[ NEXT_STATE, 1 :=\<^sub>2 V_PROC]"
  shows   "inv_nstate (fst tw' + 1, snd tw')"
proof -
  have "fst tw' = fst tw"
    unfolding tw'_def worldline_upd2_def worldline_upd_def by auto
  have "wline_of tw' NEXT_STATE (fst tw + 1) = V_PROC"
    unfolding tw'_def worldline_upd2_def worldline_upd_def by auto
  moreover have "wline_of (get_time tw' + 1, snd tw') STATE (get_time (get_time tw' + 1, snd tw') - 1) = V_PROC"
    using assms(2) snd_worldline_upd2 unfolding fst_conv `fst tw' = fst tw` comp_def snd_conv 
    by (simp add: snd_worldline_upd2 assms(1) tw'_def)
  ultimately show ?thesis
    using assms(2) snd_worldline_upd2[OF sig.simps(442)] unfolding inv_nstate_def `fst tw' = fst tw`  tw'_def 
    by auto
qed

lemma inv_nstate_vproc_false:
  fixes tw
  assumes " snd (snd tw) STATE (fst tw) = V_PROC"
  assumes " snd (snd tw) CTR_NEQ_0 (get_time tw) \<noteq> Bv True"
  defines "tw' \<equiv> tw[ NEXT_STATE, 1 :=\<^sub>2 V_POST]"
  assumes "wityping \<Gamma> (snd tw)"
  shows   "inv_nstate (fst tw' + 1, snd tw')"
proof -
  have assms2: "snd (snd tw) CTR_NEQ_0 (fst tw) = Bv False"
    using `wityping \<Gamma> (snd tw)` 
    by (smt assms(2) cosine_locale_axioms cosine_locale_def ty.distinct(1) type_of.elims val.inject(1) wityping_def wtyping_def)
  have "fst tw' = fst tw"
    unfolding tw'_def worldline_upd2_def worldline_upd_def by auto
  have "wline_of tw' NEXT_STATE (fst tw + 1) = V_POST"
    unfolding tw'_def worldline_upd2_def worldline_upd_def by auto
  moreover have "wline_of (get_time tw' + 1, snd tw') STATE (get_time (get_time tw' + 1, snd tw') - 1) = V_PROC"
    using assms(2) snd_worldline_upd2 unfolding fst_conv `fst tw' = fst tw` comp_def snd_conv 
    by (simp add: snd_worldline_upd2 assms(1) tw'_def)
  ultimately show ?thesis
    using assms2 snd_worldline_upd2[OF sig.simps(442)] unfolding inv_nstate_def `fst tw' = fst tw`  tw'_def 
    by auto
qed

lemma inv_nstate_vpost:
  fixes tw
  assumes " snd (snd tw) STATE (fst tw) = V_POST"
  defines "tw' \<equiv> tw[ NEXT_STATE, 1 :=\<^sub>2 V_WAIT]"
  shows   "inv_nstate (fst tw' + 1, snd tw')"
proof -
  have "fst tw' = fst tw"
    unfolding tw'_def worldline_upd2_def worldline_upd_def by auto
  have "wline_of tw' NEXT_STATE (fst tw + 1) = V_WAIT"
    unfolding tw'_def worldline_upd2_def worldline_upd_def by auto
  moreover have "wline_of (get_time tw' + 1, snd tw') STATE (get_time (get_time tw' + 1, snd tw') - 1) = V_POST"
    using assms(2) snd_worldline_upd2 unfolding fst_conv `fst tw' = fst tw` comp_def snd_conv 
    by (simp add: snd_worldline_upd2 assms(1))
  ultimately show ?thesis
    unfolding inv_nstate_def `fst tw' = fst tw` by auto
qed

lemma inv_nstate_others:
  fixes tw
  assumes " snd (snd tw) STATE (fst tw) \<noteq> V_INIT"
  assumes " snd (snd tw) STATE (fst tw) \<noteq> V_WAIT"
  assumes " snd (snd tw) STATE (fst tw) \<noteq> V_PRE"
  assumes " snd (snd tw) STATE (fst tw) \<noteq> V_PROC"
  assumes " snd (snd tw) STATE (fst tw) \<noteq> V_POST"
  defines "tw' \<equiv> tw[ NEXT_STATE, 1 :=\<^sub>2 V_INIT]"
  shows   "inv_nstate (fst tw' + 1, snd tw')"
proof -
  have "fst tw' = fst tw"
    unfolding tw'_def worldline_upd2_def worldline_upd_def by auto
  have "wline_of tw' NEXT_STATE (fst tw + 1) = V_INIT"
    unfolding tw'_def worldline_upd2_def worldline_upd_def by auto
  moreover have "wline_of (get_time tw' + 1, snd tw') STATE (get_time (get_time tw' + 1, snd tw') - 1) \<noteq> V_INIT"
            and "wline_of (get_time tw' + 1, snd tw') STATE (get_time (get_time tw' + 1, snd tw') - 1) \<noteq> V_WAIT"
            and "wline_of (get_time tw' + 1, snd tw') STATE (get_time (get_time tw' + 1, snd tw') - 1) \<noteq> V_PRE"
            and "wline_of (get_time tw' + 1, snd tw') STATE (get_time (get_time tw' + 1, snd tw') - 1) \<noteq> V_PROC"
            and "wline_of (get_time tw' + 1, snd tw') STATE (get_time (get_time tw' + 1, snd tw') - 1) \<noteq> V_POST"
    using assms(2) snd_worldline_upd2 unfolding fst_conv `fst tw' = fst tw` comp_def snd_conv 
    by (simp add: snd_worldline_upd2 assms)+
  ultimately show ?thesis
    unfolding inv_nstate_def `fst tw' = fst tw` fst_conv 
    by (simp_all split: val.splits signedness.splits list.splits bool.splits)
qed

lemma correctness_nstate:
  "\<Gamma> \<turnstile>\<^sub>s \<lbrace>\<lambda>tw. inv_nstate tw \<and> inv_nstate2 tw\<rbrace> next_state \<lbrace>\<lambda>tw. inv_nstate tw \<and> inv_nstate2 tw\<rbrace>"
  apply (rule While_Suc)
  apply (rule Conseq'[where P="wp3_conc \<Gamma> next_state (\<lambda>tw. inv_nstate  (fst tw + 1, snd tw) \<and> 
                                                           inv_nstate2 (fst tw + 1, snd tw))", rotated])
  apply (rule wp3_conc_is_pre, rule conc_stmt_wf_next_state, rule nonneg_delay_conc_next_state, rule cwt_ns, simp)
  unfolding next_state_def wp3_conc_single'[OF cwt_ns[unfolded next_state_def] nonneg_delay_conc_next_state[unfolded next_state_def]] wp3_fun.simps(4-5)
  apply (rule, rule, unfold if_bool_eq_conj, rule, rule, rule_tac[2] impI, rule_tac[2] conjI, rule_tac[2] impI) 
  apply (rule_tac[3] impI, rule_tac[3] conjI, rule_tac[3] impI) apply (rule_tac[4] impI, rule_tac[4] conjI, rule_tac[4] impI)
  apply (rule_tac[5] impI, rule_tac[5] conjI, rule_tac[5] impI) apply (rule_tac[6] impI, rule_tac[6] conjI, rule_tac[6] impI, rule_tac[7] impI)
  unfolding wp3_fun.simps(2) fst_worldline_upd2 eval_world_raw.simps wp3_fun.simps(7)
  subgoal using inv_nstate2_preserved inv_nstate_preserved by blast
  subgoal using inv_nstate2 inv_nstate_vinit by auto
  subgoal using inv_nstate2 inv_nstate_vwait_false inv_nstate_vwait_true by auto
  subgoal using inv_nstate2 inv_nstate_vpre by auto
  subgoal using inv_nstate2 inv_nstate_vproc_false inv_nstate_vproc_true by auto
  subgoal using inv_nstate2 inv_nstate_vpost by auto
  subgoal using inv_nstate2 inv_nstate_others by auto
  done

section \<open>Functional specification of @{term "next_common"}\<close>

abbreviation bin_of_at :: "sig \<Rightarrow> nat \<Rightarrow> nat \<times> sig worldline_init \<Rightarrow> int" ("bin'_of (1_) at'_time (1_) on (1_)") where
  "bin_of_at sig t tw \<equiv> sbl_to_bin (lof_wline tw sig t)"

term "bin_of NEXT_COMMON at_time fst tw on tw"

definition inv_ncommon :: "sig assn2" where
  "inv_ncommon tw = ((bin_of NEXT_COMMON at_time fst tw on tw) = 
                      (case wline_of tw STATE (fst tw - 1) of    
                       V_INIT \<Rightarrow> 0 |
                       V_WAIT \<Rightarrow> (if bof_wline tw INREADY (fst tw - 1) then (bin_of INPUT at_time fst tw - 1 on tw) else (bin_of COMMON at_time (fst tw - 1) on tw)) | 
                       V_PRE  \<Rightarrow> sbintrunc 31 (- (sbl_to_bin (nths (lof_wline tw SQUARE_TEMP (fst tw - 1)) {1 .. 32})))  |
                       V_PROC \<Rightarrow> sbintrunc 31 (- bin_of COMMON at_time fst tw - 1 on tw) |
                       _      \<Rightarrow>   bin_of COMMON at_time fst tw - 1 on tw 
                    ))"

definition inv_ncommon2 :: "sig assn2" where
  "inv_ncommon2 tw \<equiv> disjnt {STATE, COMMON, INREADY, INPUT, SQUARE_TEMP} (event_of tw) \<longrightarrow> 
                          (\<forall>i > fst tw. wline_of tw NEXT_COMMON i = wline_of tw NEXT_COMMON (fst tw))"


lemma inv_ncommon2_preserved:
  "\<And>tw. inv_ncommon2 tw \<and> (disjnt {STATE, COMMON, INREADY, INPUT, SQUARE_TEMP} (event_of tw)) \<Longrightarrow> inv_ncommon2 (fst tw + 1, snd tw)"
  unfolding inv_ncommon2_def by auto

lemma inv_ncommon_preserved:
  "\<And>tw. inv_ncommon tw \<and> inv_ncommon2 tw \<and>  (disjnt {STATE, COMMON, INREADY, INPUT, SQUARE_TEMP} (event_of tw)) \<Longrightarrow> inv_ncommon (fst tw + 1, snd tw)"
proof -
  fix tw
  assume "inv_ncommon tw \<and> inv_ncommon2 tw \<and> (disjnt {STATE, COMMON, INREADY, INPUT, SQUARE_TEMP} (event_of tw))"
  hence "inv_ncommon tw" "inv_ncommon2 tw" and *: "(disjnt {STATE, COMMON, INREADY, INPUT, SQUARE_TEMP} (event_of tw))"
    by auto
  have eq0: "wline_of tw STATE (fst tw) = wline_of tw STATE (fst tw - 1)" and 
       eq1: "wline_of tw INREADY (fst tw) = wline_of tw INREADY (fst tw - 1)" and 
       eq2: "wline_of tw INPUT (fst tw) = wline_of tw INPUT (fst tw - 1)" and 
       eq3: "wline_of tw COMMON (fst tw) = wline_of tw COMMON (fst tw - 1)" and
       eq4: "wline_of tw SQUARE_TEMP (fst tw) = wline_of tw SQUARE_TEMP (fst tw - 1)"
    using * unfolding event_of_alt_def by (smt diff_0_eq_0 disjnt_insert1 mem_Collect_eq)+
  have "  bin_of NEXT_COMMON at_time fst tw + 1 on tw = bin_of NEXT_COMMON at_time fst tw on tw"
    using `inv_ncommon2 tw` * unfolding inv_ncommon2_def  by (simp add: next_time_world_at_least) 
  also have "... = (case wline_of tw STATE (fst tw - 1) of    
                                         V_INIT \<Rightarrow> 0 |
                                         V_WAIT \<Rightarrow> (if bof_wline tw INREADY (fst tw - 1) then (bin_of INPUT at_time fst tw - 1 on tw) else (bin_of COMMON at_time (fst tw - 1) on tw)) | 
                                         V_PRE  \<Rightarrow> sbintrunc 31 (- (sbl_to_bin (nths (lof_wline tw SQUARE_TEMP (fst tw - 1)) {1 .. 32})))  |
                                         V_PROC \<Rightarrow> sbintrunc 31 (- bin_of COMMON at_time fst tw - 1 on tw) |
                                         _      \<Rightarrow>   bin_of COMMON at_time fst tw - 1 on tw )"
    using `inv_ncommon tw` unfolding inv_ncommon_def by auto     
  also have "... = (case wline_of tw STATE (fst tw) of    
                                         V_INIT \<Rightarrow> 0 |
                                         V_WAIT \<Rightarrow> (if bof_wline tw INREADY (fst tw) then (bin_of INPUT at_time fst tw on tw) else (bin_of COMMON at_time (fst tw) on tw)) | 
                                         V_PRE  \<Rightarrow> sbintrunc 31 (- (sbl_to_bin (nths (lof_wline tw SQUARE_TEMP (fst tw)) {1 .. 32})))  |
                                         V_PROC \<Rightarrow> sbintrunc 31 (- bin_of COMMON at_time fst tw on tw) |
                                         _      \<Rightarrow>   bin_of COMMON at_time fst tw on tw )"
    unfolding eq0 eq1 eq2 eq3 eq4 by auto
  finally show "inv_ncommon (fst tw + 1, snd tw)"
    unfolding inv_ncommon_def fst_conv comp_def snd_conv 
    by (simp_all split:val.splits signedness.splits list.splits bool.splits)  
qed

lemma inv_ncommon2: 
  fixes tw v
  defines "tw' \<equiv> tw[NEXT_COMMON, 1 :=\<^sub>2 v]"
  shows   "inv_ncommon2 (fst tw' + 1, snd tw')"
  unfolding inv_ncommon2_def tw'_def worldline_upd2_def worldline_upd_def by auto

abbreviation lval_of_at_on :: "sig \<Rightarrow> nat \<Rightarrow> nat \<times> sig worldline_init \<Rightarrow> val" ("value'_of (1_) at'_time (1_) on (1_)") where
  "lval_of_at_on sig t tw \<equiv> wline_of tw sig t"

abbreviation lval_of_at :: "sig \<Rightarrow> nat \<times> sig worldline_init \<Rightarrow> val" ("curr'_value'_of (1_) on (1_)") where
  "lval_of_at sig tw \<equiv> wline_of tw sig (fst tw)"

lemma inv_ncommon_vwait_true:
  fixes tw
  assumes " curr_value_of STATE on tw = V_WAIT"
  assumes " curr_value_of INREADY on tw = Bv True"
  defines "tw' \<equiv> tw[ NEXT_COMMON, 1 :=\<^sub>2 curr_value_of INPUT on tw]"
  shows   "inv_ncommon (fst tw' + 1, snd tw')"
proof -
  have "fst tw' = fst tw"
    unfolding tw'_def worldline_upd2_def worldline_upd_def by auto
  have "bin_of NEXT_COMMON at_time (fst tw + 1) on tw' = bin_of INPUT at_time fst tw on tw"
    unfolding tw'_def worldline_upd2_def worldline_upd_def by auto
  moreover have "wline_of (get_time tw' + 1, snd tw') STATE (get_time (get_time tw' + 1, snd tw') - 1) = V_WAIT"
    using assms(2) snd_worldline_upd2 unfolding fst_conv `fst tw' = fst tw` comp_def snd_conv 
    by (metis assms(1) comp_eq_dest_lhs diff_add_inverse2 sig.distinct(423) tw'_def)
  ultimately show ?thesis
    using assms(2) unfolding inv_ncommon_def `fst tw' = fst tw`  
    by (auto simp add: tw'_def worldline_upd2_def worldline_upd_def)
qed

lemma inv_ncommon_vwait_false:
  fixes tw
  assumes " curr_value_of STATE on tw = V_WAIT"
  assumes " curr_value_of INREADY on tw \<noteq> Bv True"
  defines "tw' \<equiv> tw[ NEXT_COMMON, 1 :=\<^sub>2 curr_value_of COMMON on tw]"
  assumes "wityping \<Gamma> (snd tw)"
  shows   "inv_ncommon (fst tw' + 1, snd tw')"
proof -
  have assms2: "curr_value_of INREADY on tw = Bv False"
    using `wityping \<Gamma> (snd tw)` 
    by (smt assms(2) cosine_locale_axioms cosine_locale_def o_apply ty.distinct(1) type_of.elims wityping_def wtyping_def)
  have "fst tw' = fst tw"
    unfolding tw'_def worldline_upd2_def worldline_upd_def by auto
  have "bin_of NEXT_COMMON at_time (fst tw + 1) on tw' = bin_of COMMON at_time fst tw on tw"
    unfolding tw'_def worldline_upd2_def worldline_upd_def by auto
  moreover have "wline_of (get_time tw' + 1, snd tw') STATE (get_time (get_time tw' + 1, snd tw') - 1) = V_WAIT"
    using assms(2) snd_worldline_upd2 unfolding fst_conv `fst tw' = fst tw` comp_def snd_conv 
    by (metis assms(1) comp_eq_dest_lhs diff_add_inverse2 sig.distinct(423) tw'_def)
  ultimately show ?thesis
    using assms2 unfolding inv_ncommon_def `fst tw' = fst tw`  
    by (auto simp add: tw'_def worldline_upd2_def worldline_upd_def)
qed

lemma sbl_to_bin_to_bl:
  "sbl_to_bin (to_bl (w :: 'a :: len word)) = sint w"
  unfolding sbl_to_bin_alt_def to_bl_bin sint_uint
  by auto

lemma [simp]: "sint (1::32 word) = 1"
  by eval

lemma inv_ncommon_vpre:
  fixes tw
  assumes " curr_value_of STATE on tw = V_PRE"
  defines "tw' \<equiv> tw[ NEXT_COMMON, 1 :=\<^sub>2 eval_world_raw2 tw (Badd (Bnot (Bslice SQUARE_TEMP 62 31)) ONE)]"
  assumes "wityping \<Gamma> (snd tw)"
  shows   "inv_ncommon (fst tw' + 1, snd tw')"
proof -
  have "fst tw' = fst tw"
    unfolding tw'_def worldline_upd2_def worldline_upd_def by auto
  have sqty: "type_of (snd (snd tw) SQUARE_TEMP (get_time tw)) = Lty Sig 64"
    using `wityping \<Gamma> (snd tw)` cosine_locale_axioms unfolding wityping_def wtyping_def cosine_locale_def
    by auto
  hence len: "length (lval_of (wline_of tw SQUARE_TEMP (get_time tw))) = 64"
    using `wityping \<Gamma> (snd tw)` 
    by (metis comp_apply ty.distinct(1) ty.inject type_of.elims val.sel(3))
  have len': "(length (nths (lval_of (curr_value_of SQUARE_TEMP on tw)) {Suc 0..32})) = 32"
    unfolding length_nths len using card_slice[of "62" "64" "31"] by auto
  have "(bin_of NEXT_COMMON at_time (fst tw + 1) on tw') = (sbl_to_bin o lval_of) (eval_world_raw2 tw (Badd (Bnot (Bslice SQUARE_TEMP 62 31)) ONE))"
    unfolding tw'_def worldline_upd2_def worldline_upd_def by auto
  also have "... =  sbl_to_bin (bin_to_bl (max (length (nths (lval_of (curr_value_of SQUARE_TEMP on tw)) {Suc 0..32})) 32) 
                                              (sbl_to_bin (map Not (nths (lval_of (curr_value_of SQUARE_TEMP on tw)) {Suc 0..32})) + sbl_to_bin (to_bl (1::32 word))))"
    using sqty unfolding eval_world_raw.simps comp_def eval_arith.simps by (auto split:val.splits signedness.splits simp del: bin_to_bl_def)
  also have "... = sbl_to_bin (bin_to_bl 32 (sbl_to_bin (map Not (nths (lval_of (wline_of tw SQUARE_TEMP (get_time tw))) {Suc 0..32})) + 1))"
    unfolding len' sbl_to_bin_to_bl by auto
  also have "... =  sbl_to_bin (bin_to_bl 32 (- (sbl_to_bin (nths (lof_wline tw SQUARE_TEMP (fst tw)) {1 .. 32}))))"
    unfolding len' using  len'  by (simp add: uminus_alt)
  also have "... = sbintrunc 31 (- (sbl_to_bin (nths (lof_wline tw SQUARE_TEMP (fst tw)) {1 .. 32})))"
    using  sbin_bl_bin_sbintruc by auto
  finally have "(bin_of NEXT_COMMON at_time (fst tw + 1) on tw') = 
                sbintrunc 31 (- (sbl_to_bin (nths (lof_wline tw SQUARE_TEMP (fst tw)) {1 .. 32})))"
    by auto
  moreover have "wline_of (get_time tw' + 1, snd tw') STATE (get_time (get_time tw' + 1, snd tw') - 1) = V_PRE"
    using assms(2) snd_worldline_upd2 unfolding fst_conv `fst tw' = fst tw` comp_def snd_conv 
    by (metis assms(1) comp_eq_dest_lhs diff_add_inverse2 sig.distinct(423) tw'_def)
  ultimately show ?thesis
    using assms(2) unfolding inv_ncommon_def `fst tw' = fst tw`  
    by (auto simp add: tw'_def worldline_upd2_def worldline_upd_def)
qed

lemma inv_ncommon_vproc:
  fixes tw
  assumes " curr_value_of STATE on tw = V_PROC"
  defines "tw' \<equiv> tw[ NEXT_COMMON, 1 :=\<^sub>2 eval_world_raw2 tw (Badd (Bnot (Bsig COMMON)) ONE)]"
  assumes "wityping \<Gamma> (snd tw)"
  shows   "inv_ncommon (fst tw' + 1, snd tw')"
proof -
  have "fst tw' = fst tw"
    unfolding tw'_def worldline_upd2_def worldline_upd_def by auto
  have coty: "type_of (curr_value_of COMMON on tw) = Lty Sig 32"
    using `wityping \<Gamma> (snd tw)` cosine_locale_axioms unfolding wityping_def wtyping_def cosine_locale_def
    by auto
  hence len: "length (lval_of (wline_of tw COMMON (get_time tw))) = 32"
    using `wityping \<Gamma> (snd tw)`
    by (metis comp_apply ty.distinct(1) ty.inject type_of.elims val.sel(3))
  have "(bin_of NEXT_COMMON at_time (fst tw + 1) on tw') = (sbl_to_bin o lval_of) (eval_world_raw2 tw (Badd (Bnot (Bsig COMMON)) ONE))"
    unfolding tw'_def worldline_upd2_def worldline_upd_def by auto
  also have "... =  sbl_to_bin (bin_to_bl 32 (sbl_to_bin (map Not (lval_of curr_value_of COMMON on tw)) + sbl_to_bin (to_bl (1 :: 32 word))))"
    using coty unfolding eval_world_raw.simps comp_def eval_arith.simps by (auto split:val.splits signedness.splits simp del: bin_to_bl_def)
  also have "... =  sbl_to_bin (bin_to_bl 32 (sbl_to_bin (map Not (lval_of curr_value_of COMMON on tw)) + 1))"
    unfolding sbl_to_bin_to_bl by auto
  also have "... =  sbl_to_bin (bin_to_bl 32 ( - sbl_to_bin (lval_of (wline_of tw COMMON (get_time tw)))))"
    using  len  uminus_alt[where bs="lval_of curr_value_of COMMON on tw"] by auto
  also have "... = sbintrunc 31 ( - sbl_to_bin (lval_of (wline_of tw COMMON (get_time tw))))"
    using  sbin_bl_bin_sbintruc by auto
  finally have "(bin_of NEXT_COMMON at_time (fst tw + 1) on tw') = 
                sbintrunc 31 ( - sbl_to_bin (lval_of (wline_of tw COMMON (get_time tw))))"
    by auto
  moreover have "wline_of (get_time tw' + 1, snd tw') STATE (get_time (get_time tw' + 1, snd tw') - 1) = V_PROC"
    using assms(2) snd_worldline_upd2 unfolding fst_conv `fst tw' = fst tw` comp_def snd_conv 
    by (metis assms(1) comp_eq_dest_lhs diff_add_inverse2 sig.distinct(423) tw'_def)
  ultimately show ?thesis
    using assms(2) unfolding inv_ncommon_def `fst tw' = fst tw`  
    by (auto simp add: tw'_def worldline_upd2_def worldline_upd_def)
qed

lemma inv_ncommon_vinit:
  fixes tw
  assumes " curr_value_of STATE on tw = V_INIT"
  defines "tw' \<equiv> tw[ NEXT_COMMON, 1 :=\<^sub>2 V_ZERO32]"
  shows   "inv_ncommon (fst tw' + 1, snd tw')"
proof -
  have "fst tw' = fst tw"
    unfolding tw'_def worldline_upd2_def worldline_upd_def by auto
  have "bin_of NEXT_COMMON at_time (fst tw + 1) on tw' = 0"
    unfolding tw'_def worldline_upd2_def worldline_upd_def by auto
  moreover have "wline_of (get_time tw' + 1, snd tw') STATE (get_time (get_time tw' + 1, snd tw') - 1) = V_INIT"
    using assms(2) snd_worldline_upd2 unfolding fst_conv `fst tw' = fst tw` comp_def snd_conv 
    by (metis assms(1) comp_eq_dest_lhs diff_add_inverse2 sig.distinct(423) tw'_def)
  ultimately show ?thesis
    using assms(2) unfolding inv_ncommon_def `fst tw' = fst tw`  
    by (auto simp add: tw'_def worldline_upd2_def worldline_upd_def)
qed

lemma inv_ncommon_others:
  fixes tw
  assumes " snd (snd tw) STATE (fst tw) \<noteq> V_WAIT"
  assumes " snd (snd tw) STATE (fst tw) \<noteq> V_PRE"
  assumes " snd (snd tw) STATE (fst tw) \<noteq> V_PROC"
  assumes " snd (snd tw) STATE (fst tw) \<noteq> V_INIT"
  defines "tw' \<equiv> tw[ NEXT_COMMON, 1 :=\<^sub>2  eval_world_raw2 tw (Bsig COMMON)]"
  shows   "inv_ncommon (fst tw' + 1, snd tw')"
proof -
  have "fst tw' = fst tw"
    unfolding tw'_def worldline_upd2_def worldline_upd_def by auto
  have "wline_of tw' NEXT_COMMON (fst tw + 1) = curr_value_of COMMON on tw"
    unfolding tw'_def worldline_upd2_def worldline_upd_def by auto
  moreover have "wline_of (get_time tw' + 1, snd tw') STATE (get_time (get_time tw' + 1, snd tw') - 1) \<noteq> V_WAIT"
            and "wline_of (get_time tw' + 1, snd tw') STATE (get_time (get_time tw' + 1, snd tw') - 1) \<noteq> V_PRE"
            and "wline_of (get_time tw' + 1, snd tw') STATE (get_time (get_time tw' + 1, snd tw') - 1) \<noteq> V_PROC"
            and "wline_of (get_time tw' + 1, snd tw') STATE (get_time (get_time tw' + 1, snd tw') - 1) \<noteq> V_INIT"
    using assms(2) snd_worldline_upd2 unfolding fst_conv `fst tw' = fst tw` comp_def snd_conv 
    by (simp add: snd_worldline_upd2 assms)+
  ultimately show ?thesis
    unfolding inv_ncommon_def `fst tw' = fst tw` fst_conv tw'_def worldline_upd2_def worldline_upd_def
    by (simp_all split: val.splits signedness.splits list.splits bool.splits)
qed

lemma correctness_ncommon:
  "\<Gamma> \<turnstile>\<^sub>s \<lbrace>\<lambda>tw. inv_ncommon tw \<and> inv_ncommon2 tw\<rbrace> next_common \<lbrace>\<lambda>tw. inv_ncommon tw \<and> inv_ncommon2 tw\<rbrace>"
  apply (rule While_Suc)
  apply (rule Conseq'[where P="wp3_conc \<Gamma> next_common (\<lambda>tw. inv_ncommon  (fst tw + 1, snd tw) \<and> 
                                                           inv_ncommon2 (fst tw + 1, snd tw))", rotated])
  apply (rule wp3_conc_is_pre, rule conc_stmt_wf_next_common, rule nonneg_delay_conc_next_common, rule cwt_nc, simp)
  unfolding next_common_def wp3_conc_single'[OF cwt_nc[unfolded next_common_def] nonneg_delay_conc_next_common[unfolded next_common_def]] wp3_fun.simps(4-5)
  apply (rule, rule, unfold if_bool_eq_conj, rule, rule, rule_tac[2] impI, rule_tac[2] conjI, rule_tac[2] impI) 
  apply (rule_tac[3] impI, rule_tac[3] conjI, rule_tac[3] impI) apply (rule_tac[4] impI, rule_tac[4] conjI, rule_tac[4] impI)
  apply (rule_tac[5] impI, rule_tac[5] conjI, rule_tac[5] impI, rule_tac[6] impI)
  unfolding wp3_fun.simps(2) fst_worldline_upd2  wp3_fun.simps(7)
  subgoal using inv_ncommon2_preserved inv_ncommon_preserved by auto
  subgoal unfolding eval_world_raw.simps using inv_ncommon2 inv_ncommon_vwait_false inv_ncommon_vwait_true by auto
  subgoal unfolding eval_world_raw.simps(10) using inv_ncommon2 inv_ncommon_vpre by auto
  subgoal unfolding eval_world_raw.simps(10) using inv_ncommon2 inv_ncommon_vproc by auto
  subgoal unfolding eval_world_raw.simps using inv_ncommon2 inv_ncommon_vinit by auto
  subgoal unfolding eval_world_raw.simps using inv_ncommon2 inv_ncommon_others by auto
  done

lemma init_ensures_ncommon:
  "init_sim2_hoare_wt \<Gamma> (\<lambda>tw. fst tw = 0) next_common (\<lambda>tw. inv_ncommon tw \<and> inv_ncommon2 tw)"
  unfolding next_common_def
  apply (rule AssignI_suc, rule SingleI)
  apply (rule Conseq3[where Q="\<lambda>tw. inv_ncommon (fst tw + 1, snd tw) \<and> inv_ncommon2 (fst tw + 1, snd tw)", rotated])
  apply (rule wp3_fun_is_pre[OF seq_wt_next_common[unfolded next_common_def conc_stmt.sel(4)] nonneg_delay_next_common[unfolded next_common_def conc_stmt.sel(4)]], simp)
  apply (rule, rule, unfold wp3_fun.simps(4), unfold if_bool_eq_conj)
  apply (rule conjI, rule impI)+
  apply (rule_tac[2] conjI | rule_tac[2] impI)+ apply (rule_tac[3] conjI | rule_tac[3] impI)+
  apply (rule_tac[4] conjI | rule_tac[4] impI)+ apply (rule_tac[5] conjI | rule_tac[5] impI)+
  subgoal unfolding wp3_fun.simps using inv_ncommon_vwait_true inv_ncommon_vwait_false inv_ncommon2 
    by (metis comp_apply eval_world_raw.simps(10) eval_world_raw.simps(21))
  subgoal unfolding wp3_fun.simps using inv_ncommon2 inv_ncommon_vpre 
    by (metis comp_apply eval_world_raw.simps(10) eval_world_raw.simps(21)) 
  subgoal unfolding wp3_fun.simps using inv_ncommon2 inv_ncommon_vproc 
    by (metis comp_apply eval_world_raw.simps(10) eval_world_raw.simps(21)) 
  subgoal unfolding wp3_fun.simps using inv_ncommon2 inv_ncommon_vinit
    by (metis comp_apply eval_world_raw.simps(10) eval_world_raw.simps(21)) 
  subgoal unfolding wp3_fun.simps using inv_ncommon2 inv_ncommon_others
    by (metis eval_world_raw.simps(10) eval_world_raw.simps(21)) 
  done

lemma 
  assumes "sim_fin2 w (i + 1) next_common tw'" and "wityping \<Gamma> w"
  shows "inv_ncommon tw'"
  using grand_correctness[OF assms conc_stmt_wf_next_common cwt_nc nonneg_delay_conc_next_common correctness_ncommon init_ensures_ncommon]
  by auto
    
section \<open>Functional specification of @{term "squaring"}\<close>

definition inv_sqr :: "sig assn2" where
  "inv_sqr tw = (bin_of SQUARE_TEMP at_time fst tw on tw = sbintrunc 63 ((bin_of COMMON at_time fst tw - 1 on tw)\<^sup>2))"

definition inv_sqr2 :: "sig assn2" where
  "inv_sqr2 tw \<equiv> disjnt {COMMON} (event_of tw) \<longrightarrow> (\<forall>i > fst tw. bin_of SQUARE_TEMP at_time i on tw = bin_of SQUARE_TEMP at_time fst tw on tw)"

lemma inv_sqr2_preserved:
  "\<And>tw. inv_sqr2 tw \<and> (disjnt {COMMON} (event_of tw)) \<Longrightarrow> inv_sqr2 (fst tw + 1, snd tw)"
  unfolding inv_sqr2_def by auto

lemma inv_sqr_preserved:
  "\<And>tw. inv_sqr tw \<and> inv_sqr2 tw \<and>  (disjnt {COMMON} (event_of tw)) \<Longrightarrow> inv_sqr (fst tw + 1, snd tw)"
proof -
  fix tw 
  assume "inv_sqr tw \<and> inv_sqr2 tw \<and>  (disjnt {COMMON} (event_of tw)) "
  hence "inv_sqr tw" and "inv_sqr2 tw" and "disjnt {COMMON} (event_of tw)"
    by auto
  hence "bin_of SQUARE_TEMP at_time fst tw + 1 on tw = bin_of SQUARE_TEMP at_time fst tw on tw"
    unfolding inv_sqr2_def by auto
  also have "... = sbintrunc 63 ((bin_of COMMON at_time fst tw - 1 on tw)\<^sup>2)"
    using `inv_sqr tw` unfolding inv_sqr_def by auto
  also have "... = sbintrunc 63 ((bin_of COMMON at_time fst tw on tw)\<^sup>2)"
    using `disjnt {COMMON} (event_of tw)` unfolding event_of_alt_def 
    by (smt disjnt_insert1 mem_Collect_eq minus_eq)
  finally show "inv_sqr (fst tw + 1, snd tw)"
    unfolding inv_sqr_def by auto
qed

lemma inv_sqr_next_time:
  fixes tw
  defines "v \<equiv> eval_world_raw2 tw (Bmult (Bsig COMMON) (Bsig COMMON))"
  defines "tw' \<equiv> tw[SQUARE_TEMP , 1 :=\<^sub>2 v]"
  assumes "wityping \<Gamma> (snd tw)"
  shows   "inv_sqr (fst tw' + 1, snd tw')"
proof -
  have *: "type_of (snd (snd tw) COMMON (fst tw)) = Lty Sig 32"
    using cosine_locale_axioms `wityping \<Gamma> (snd tw)` 
    unfolding wityping_def wtyping_def cosine_locale_def by auto
  have "bin_of SQUARE_TEMP at_time fst tw' + 1 on (fst tw' + 1, snd tw') = bin_of SQUARE_TEMP at_time fst tw' + 1 on tw'"
    unfolding fst_conv comp_def tw'_def worldline_upd2_def worldline_upd_def by auto
  also have "... = bin_of SQUARE_TEMP at_time fst tw + 1 on tw'"
    unfolding tw'_def fst_worldline_upd2 by auto
  also have "... = sbl_to_bin (lval_of v)"
    unfolding tw'_def worldline_upd2_def worldline_upd_def by auto
  also have "... = sbl_to_bin (bin_to_bl 64 ((sbl_to_bin (lval_of (curr_value_of COMMON on tw)))\<^sup>2))"
    using * unfolding v_def eval_world_raw.simps eval_arith.simps Let_def power_def by (auto split: val.splits)
  also have "... = sbintrunc 63 ((bin_of COMMON at_time fst tw on tw)\<^sup>2)"
    using sbin_bl_bin_sbintruc by auto
  also have "... = sbintrunc 63 ((bin_of COMMON at_time fst tw' on (fst tw' + 1, snd tw'))\<^sup>2)"
    unfolding tw'_def fst_worldline_upd2 comp_def worldline_upd2_def worldline_upd_def by auto
  finally show ?thesis
    unfolding inv_sqr_def by auto
qed

lemma inv_sqr2_next_time:
  fixes tw
  defines "v \<equiv> eval_world_raw2 tw (Bmult (Bsig COMMON) (Bsig COMMON))"
  defines "tw' \<equiv> tw[SQUARE_TEMP , 1 :=\<^sub>2 v]"
  shows   "inv_sqr2 (fst tw' + 1, snd tw')"
  using assms unfolding inv_sqr2_def tw'_def worldline_upd2_def worldline_upd_def by auto 
 
lemma correctness_sqr:
  "\<Gamma> \<turnstile>\<^sub>s \<lbrace>\<lambda>tw. inv_sqr tw \<and> inv_sqr2 tw\<rbrace> squaring \<lbrace>\<lambda>tw. inv_sqr tw \<and> inv_sqr2 tw\<rbrace>"
  apply (rule While_Suc)
  apply (rule Conseq'[where P="wp3_conc \<Gamma> squaring (\<lambda>tw. inv_sqr  (fst tw + 1, snd tw) \<and> 
                                                         inv_sqr2 (fst tw + 1, snd tw))", rotated])
    apply (rule wp3_conc_is_pre, rule conc_stmt_wf_squaring, rule nonneg_delay_conc_squaring, rule cwts, simp)
  unfolding squaring_def wp3_conc_single'[OF cwts[unfolded squaring_def] nonneg_delay_conc_squaring[unfolded squaring_def]] wp3_fun.simps 
  apply (rule, rule, unfold if_bool_eq_conj, rule, rule, rule_tac[2] impI) 
  subgoal using inv_sqr_preserved inv_sqr2_preserved by auto
  subgoal unfolding fst_worldline_upd2 using inv_sqr2_next_time inv_sqr_next_time  by auto
  done

lemma init_ensures_nsqr:
  "init_sim2_hoare_wt \<Gamma> (\<lambda>tw. fst tw = 0) squaring (\<lambda>tw. inv_sqr tw \<and> inv_sqr2 tw)"
  unfolding squaring_def
  apply (rule AssignI_suc, rule SingleI)
  apply (rule Conseq3[where Q="\<lambda>tw. inv_sqr (fst tw + 1, snd tw) \<and> inv_sqr2 (fst tw + 1, snd tw)", rotated])
    apply (rule wp3_fun_is_pre[OF seq_wt_squaring[unfolded squaring_def conc_stmt.sel(4)] nonneg_delay_squaring[unfolded squaring_def conc_stmt.sel(4)]], simp)
  apply (rule, rule, unfold wp3_fun.simps)
  using inv_sqr2_next_time inv_sqr_next_time by blast


lemma 
  assumes "sim_fin2 w (i + 1) squaring tw'" and "wityping \<Gamma> w"
  shows "inv_sqr tw'"
  using grand_correctness[OF assms conc_stmt_wf_squaring cwts nonneg_delay_conc_squaring correctness_sqr init_ensures_nsqr]
  by auto

section \<open>Functional specfication for @{term "next_counter"}\<close>

abbreviation ubin_of_at :: "sig \<Rightarrow> nat \<Rightarrow> nat \<times> sig worldline_init \<Rightarrow> int" ("ubin'_of (1_) at'_time (1_) on (1_)") where
  "ubin_of_at sig t tw \<equiv> bl_to_bin (lof_wline tw sig t)"

definition inv_ncounter :: "sig assn2" where  
  "inv_ncounter tw = ((ubin_of NEXT_COUNTER at_time fst tw on tw) = 
                      (case wline_of tw STATE (fst tw - 1) of    
                       V_WAIT \<Rightarrow> (if bof_wline tw INREADY (fst tw - 1) then 4 else (ubin_of COUNTER at_time (fst tw - 1) on tw)) | 
                       V_PRE  \<Rightarrow> bintrunc 3 ((ubin_of COUNTER at_time fst tw - 1 on tw) - 1)  |
                       V_PROC \<Rightarrow> (if bof_wline tw CTR_NEQ_0 (fst tw - 1) then bintrunc 3 ((ubin_of COUNTER at_time fst tw - 1 on tw) - 1) else (ubin_of COUNTER at_time (fst tw - 1) on tw)) |
                       V_INIT \<Rightarrow> 0 |
                       _      \<Rightarrow>   ubin_of COUNTER at_time fst tw - 1 on tw 
                      ))"

definition inv_ncounter2 :: "sig assn2" where
  "inv_ncounter2 tw \<equiv> disjnt {STATE, INREADY, CTR_NEQ_0, COUNTER} (event_of tw) \<longrightarrow> 
                          (\<forall>i > fst tw. wline_of tw NEXT_COUNTER i = wline_of tw NEXT_COUNTER (fst tw))"

lemma inv_ncounter2_preserved:
  "\<And>tw. inv_ncounter2 tw \<and> (disjnt {STATE, INREADY, CTR_NEQ_0, COUNTER} (event_of tw)) \<Longrightarrow> inv_ncounter2 (fst tw + 1, snd tw)"
  unfolding inv_ncounter2_def by auto

lemma inv_ncounter_preserved:
  "\<And>tw. inv_ncounter tw \<and> inv_ncounter2 tw \<and>  (disjnt {STATE, INREADY, CTR_NEQ_0, COUNTER} (event_of tw)) \<Longrightarrow> inv_ncounter (fst tw + 1, snd tw)"
proof -
  fix tw
  assume *: "inv_ncounter tw \<and> inv_ncounter2 tw \<and>  (disjnt {STATE, INREADY, CTR_NEQ_0, COUNTER} (event_of tw))"
  hence 0: "bof_wline tw INREADY (fst tw) = bof_wline tw INREADY (fst tw - 1)" and 
        1: "ubin_of COUNTER at_time (fst tw) on tw = ubin_of COUNTER at_time (fst tw - 1) on tw" and 
        2: "bof_wline tw CTR_NEQ_0 (fst tw) = bof_wline tw CTR_NEQ_0 (fst tw - 1)" and 
        3: "value_of STATE at_time (fst tw - 1) on tw = curr_value_of STATE on tw"
    unfolding event_of_alt_def 
    by (smt diff_0_eq_0 disjnt_insert1 mem_Collect_eq)+

  have  "inv_ncounter tw" and "inv_ncounter2 tw" and "disjnt {STATE, INREADY, CTR_NEQ_0, COUNTER} (event_of tw)"
    using * by auto
  hence "ubin_of NEXT_COUNTER at_time fst tw + 1 on tw = ubin_of NEXT_COUNTER at_time fst tw on tw"
    unfolding inv_ncounter2_def by auto
  also have "... = (case wline_of tw STATE (fst tw - 1) of    
                       V_WAIT \<Rightarrow> (if bof_wline tw INREADY (fst tw - 1) then 4 else (ubin_of COUNTER at_time (fst tw - 1) on tw)) | 
                       V_PRE  \<Rightarrow> bintrunc 3 ((ubin_of COUNTER at_time fst tw - 1 on tw) - 1)  |
                       V_PROC \<Rightarrow> (if bof_wline tw CTR_NEQ_0 (fst tw - 1) then bintrunc 3 ((ubin_of COUNTER at_time fst tw - 1 on tw) - 1) else (ubin_of COUNTER at_time (fst tw - 1) on tw)) |
                       V_INIT \<Rightarrow> 0 |
                       _      \<Rightarrow>   ubin_of COUNTER at_time fst tw - 1 on tw 
                      )"
    using `inv_ncounter tw` unfolding inv_ncounter_def by auto
  also have "... = (case curr_value_of STATE on tw of    
                       V_WAIT \<Rightarrow> (if bof_wline tw INREADY (fst tw) then 4 else (ubin_of COUNTER at_time (fst tw) on tw)) | 
                       V_PRE  \<Rightarrow> bintrunc 3 ((ubin_of COUNTER at_time fst tw on tw) - 1)  |
                       V_PROC \<Rightarrow> (if bof_wline tw CTR_NEQ_0 (fst tw) then bintrunc 3 ((ubin_of COUNTER at_time fst tw on tw) - 1) else (ubin_of COUNTER at_time (fst tw) on tw)) |
                       V_INIT \<Rightarrow> 0 |
                       _      \<Rightarrow>   ubin_of COUNTER at_time fst tw on tw 
                      )"
    unfolding 0 1 2 3 by auto
  finally show "inv_ncounter (fst tw + 1, snd tw)"
    unfolding inv_ncounter_def by (simp_all split: val.splits signedness.splits list.splits bool.splits)
qed

lemma inv_ncounter_vwait_true:
  fixes tw
  assumes " curr_value_of STATE on tw = V_WAIT"
  assumes " curr_value_of INREADY on tw = Bv True"
  defines "tw' \<equiv> tw[ NEXT_COUNTER, 1 :=\<^sub>2 Lv Uns (to_bl (4 :: 3 word))]"
  shows   "inv_ncounter (fst tw' + 1, snd tw')"
proof -        
  have *: "curr_value_of STATE on tw' = V_WAIT"
    using assms(1) unfolding tw'_def worldline_upd2_def worldline_upd_def by auto
  have **: "bof_wline tw' INREADY (fst tw')"
    using assms(2) unfolding tw'_def worldline_upd2_def worldline_upd_def by auto
  have "(ubin_of NEXT_COUNTER at_time fst tw' + 1 on (fst tw' + 1, snd tw')) =  (ubin_of NEXT_COUNTER at_time fst tw + 1 on tw')"  
    unfolding tw'_def worldline_upd2_def worldline_upd_def by auto
  also have "... = 4"
    unfolding tw'_def worldline_upd2_def worldline_upd_def by auto eval
  finally show ?thesis
    using * ** unfolding inv_ncounter_def fst_conv comp_def snd_conv by auto
qed

lemma inv_ncounter_vwait_false:
  fixes tw
  assumes " curr_value_of STATE on tw = V_WAIT"
  assumes " curr_value_of INREADY on tw \<noteq> Bv True"
  defines "tw' \<equiv> tw[ NEXT_COUNTER, 1 :=\<^sub>2 eval_world_raw2 tw (Bsig COUNTER)]"
  assumes "wityping \<Gamma> (snd tw)"
  shows   "inv_ncounter (fst tw' + 1, snd tw')"
proof - 
  have *: "curr_value_of STATE on tw' = V_WAIT"
    using assms(1) unfolding tw'_def worldline_upd2_def worldline_upd_def by auto
  have "type_of ( snd (snd tw) INREADY (get_time tw)) = Bty"
    using assms(4) cosine_locale_axioms unfolding wityping_def wtyping_def cosine_locale_def
    by auto
  hence "curr_value_of INREADY on tw = Bv False"
    using assms(2)  by (smt comp_apply ty.distinct(1) type_of.elims)
  hence **: "\<not> bof_wline tw' INREADY (fst tw')"
    using assms(2) unfolding tw'_def worldline_upd2_def worldline_upd_def by auto
  have "(ubin_of NEXT_COUNTER at_time fst tw' + 1 on (fst tw' + 1, snd tw')) =  (ubin_of NEXT_COUNTER at_time fst tw + 1 on tw')"  
    unfolding tw'_def worldline_upd2_def worldline_upd_def by auto
  also have "... = ubin_of COUNTER at_time fst tw on tw"
    unfolding tw'_def worldline_upd2_def worldline_upd_def by auto
  finally show ?thesis
    using * ** unfolding tw'_def inv_ncounter_def fst_conv comp_def snd_conv worldline_upd2_def worldline_upd_def 
    by auto
qed

lemma inv_ncounter_vpre:
  fixes tw
  assumes " curr_value_of STATE on tw = V_PRE"
  defines "tw' \<equiv> tw[ NEXT_COUNTER, 1 :=\<^sub>2 eval_world_raw2 tw (Bsub (Bsig COUNTER) (Bliteral Uns (to_bl (1 :: 3 word))))]"
  assumes "wityping \<Gamma> (snd tw)"
  shows   "inv_ncounter (fst tw' + 1, snd tw')"
proof -        
  have tyc: "type_of (snd (snd tw) COUNTER (get_time tw)) = Lty Uns 3"
    using assms(3) cosine_locale_axioms unfolding  wityping_def wtyping_def cosine_locale_def by auto
  have *: "curr_value_of STATE on tw' = V_PRE"
    using assms(1) unfolding tw'_def worldline_upd2_def worldline_upd_def by auto
  have "(ubin_of NEXT_COUNTER at_time fst tw' + 1 on (fst tw' + 1, snd tw')) =  (ubin_of NEXT_COUNTER at_time fst tw + 1 on tw')"  
    unfolding tw'_def worldline_upd2_def worldline_upd_def by auto
  also have "... = bl_to_bin (bin_to_bl 3 ((ubin_of COUNTER at_time fst tw on tw) - 1))"
    using tyc unfolding tw'_def worldline_upd2_def worldline_upd_def eval_world_raw.simps eval_arith.simps Let_def
    by (auto split: val.splits)
  also have "... = bintrunc 3 ((ubin_of COUNTER at_time fst tw on tw) - 1)"
    unfolding bin_bl_bin by auto
  finally show ?thesis
    using * unfolding tw'_def inv_ncounter_def fst_conv comp_def snd_conv worldline_upd2_def worldline_upd_def
    by auto
qed

lemma inv_ncounter_vproc_true:
  fixes tw
  assumes " curr_value_of STATE on tw = V_PROC"
  assumes " curr_value_of CTR_NEQ_0 on tw = Bv True"
  defines "tw' \<equiv> tw[ NEXT_COUNTER, 1 :=\<^sub>2  eval_world_raw2 tw (Bsub (Bsig COUNTER) (Bliteral Uns (to_bl (1 :: 3 word))))]"
  assumes "wityping \<Gamma> (snd tw)"
  shows   "inv_ncounter (fst tw' + 1, snd tw')"
proof -
  have tyc: "type_of (snd (snd tw) COUNTER (get_time tw)) = Lty Uns 3"
    using assms(4) cosine_locale_axioms unfolding  wityping_def wtyping_def cosine_locale_def by auto
  have *: "curr_value_of STATE on tw' = V_PROC"
    using assms(1) unfolding tw'_def worldline_upd2_def worldline_upd_def by auto
  have **: "bof_wline tw' CTR_NEQ_0 (fst tw')"
    using assms(2) unfolding tw'_def worldline_upd2_def worldline_upd_def by auto
  have "(ubin_of NEXT_COUNTER at_time fst tw' + 1 on (fst tw' + 1, snd tw')) =  (ubin_of NEXT_COUNTER at_time fst tw + 1 on tw')"  
    unfolding tw'_def worldline_upd2_def worldline_upd_def by auto
  also have "... = bl_to_bin (bin_to_bl 3 ((ubin_of COUNTER at_time fst tw on tw) - 1))"
    using tyc unfolding tw'_def worldline_upd2_def worldline_upd_def by (auto split: val.splits)
  also have "... = bintrunc 3 ((ubin_of COUNTER at_time fst tw on tw) - 1)"
    unfolding bin_bl_bin by auto
  finally show ?thesis
    using * ** unfolding tw'_def inv_ncounter_def fst_conv comp_def snd_conv worldline_upd2_def worldline_upd_def 
    by auto
qed

lemma inv_ncounter_vproc_false:
  fixes tw
  assumes " curr_value_of STATE on tw = V_PROC"
  assumes " curr_value_of CTR_NEQ_0 on tw \<noteq> Bv True"
  defines "tw' \<equiv> tw[ NEXT_COUNTER, 1 :=\<^sub>2  eval_world_raw2 tw (Bsig COUNTER)]"
  assumes "wityping \<Gamma> (snd tw)"
  shows   "inv_ncounter (fst tw' + 1, snd tw')"
proof -
  have *: "curr_value_of STATE on tw' = V_PROC"
    using assms(1) unfolding tw'_def worldline_upd2_def worldline_upd_def by auto
  have "type_of ( snd (snd tw) CTR_NEQ_0 (get_time tw)) = Bty"
    using assms(4) cosine_locale_axioms unfolding wityping_def wtyping_def cosine_locale_def
    by auto
  hence "curr_value_of CTR_NEQ_0 on tw = Bv False"
    using assms(2)  by (smt comp_apply ty.distinct(1) type_of.elims)
  hence **: "\<not> bof_wline tw' CTR_NEQ_0 (fst tw')"
    using assms(2) unfolding tw'_def worldline_upd2_def worldline_upd_def by auto
  have "(ubin_of NEXT_COUNTER at_time fst tw' + 1 on (fst tw' + 1, snd tw')) =  (ubin_of NEXT_COUNTER at_time fst tw + 1 on tw')"  
    unfolding tw'_def worldline_upd2_def worldline_upd_def by auto
  also have "... = ubin_of COUNTER at_time fst tw on tw"
    unfolding tw'_def worldline_upd2_def worldline_upd_def by auto
  finally show ?thesis
    using * ** unfolding tw'_def inv_ncounter_def fst_conv comp_def snd_conv worldline_upd2_def worldline_upd_def 
    by auto
qed

lemma inv_ncounter_vinit:
  fixes tw
  assumes " curr_value_of STATE on tw = V_INIT"
  defines "tw' \<equiv> tw[ NEXT_COUNTER, 1 :=\<^sub>2 Lv Uns (to_bl (0 :: 3 word))]"
  shows   "inv_ncounter (fst tw' + 1, snd tw')"
proof -        
  have *: "curr_value_of STATE on tw' = V_INIT"
    using assms(1) unfolding tw'_def worldline_upd2_def worldline_upd_def by auto
  have "(ubin_of NEXT_COUNTER at_time fst tw' + 1 on (fst tw' + 1, snd tw')) =  (ubin_of NEXT_COUNTER at_time fst tw + 1 on tw')"  
    unfolding tw'_def worldline_upd2_def worldline_upd_def by auto
  also have "... = 0"
    unfolding tw'_def worldline_upd2_def worldline_upd_def by auto
  finally show ?thesis
    using * unfolding inv_ncounter_def fst_conv comp_def snd_conv by auto
qed

lemma inv_ncounter_others:
  fixes tw
  assumes " snd (snd tw) STATE (fst tw) \<noteq> V_WAIT"
  assumes " snd (snd tw) STATE (fst tw) \<noteq> V_PRE"
  assumes " snd (snd tw) STATE (fst tw) \<noteq> V_PROC"
  assumes " snd (snd tw) STATE (fst tw) \<noteq> V_INIT"
  defines "tw' \<equiv> tw[ NEXT_COUNTER, 1 :=\<^sub>2  eval_world_raw2 tw (Bsig COUNTER)]"
  shows   "inv_ncounter (fst tw' + 1, snd tw')"
proof -            
  have "fst tw' = fst tw"
    unfolding tw'_def worldline_upd2_def worldline_upd_def by auto
  have "wline_of tw' NEXT_COUNTER (fst tw + 1) = curr_value_of COUNTER on tw"
    unfolding tw'_def worldline_upd2_def worldline_upd_def by auto
  moreover have "wline_of (get_time tw' + 1, snd tw') STATE (get_time (get_time tw' + 1, snd tw') - 1) \<noteq> V_WAIT"
            and "wline_of (get_time tw' + 1, snd tw') STATE (get_time (get_time tw' + 1, snd tw') - 1) \<noteq> V_PRE"
            and "wline_of (get_time tw' + 1, snd tw') STATE (get_time (get_time tw' + 1, snd tw') - 1) \<noteq> V_PROC"
            and "wline_of (get_time tw' + 1, snd tw') STATE (get_time (get_time tw' + 1, snd tw') - 1) \<noteq> V_INIT"
    using assms(2) snd_worldline_upd2 unfolding fst_conv `fst tw' = fst tw` comp_def snd_conv 
    by (simp add: snd_worldline_upd2 assms)+
  ultimately show ?thesis
    unfolding inv_ncounter_def `fst tw' = fst tw` fst_conv tw'_def worldline_upd2_def worldline_upd_def
    by (simp_all split: val.splits signedness.splits list.splits bool.splits)
qed

lemma inv_ncounter2: 
  fixes tw v
  defines "tw' \<equiv> tw[NEXT_COUNTER, 1 :=\<^sub>2 v]"
  shows   "inv_ncounter2 (fst tw' + 1, snd tw')"
  unfolding inv_ncounter2_def tw'_def worldline_upd2_def worldline_upd_def by auto

lemma correctness_ncounter:
  "\<Gamma> \<turnstile>\<^sub>s \<lbrace>\<lambda>tw. inv_ncounter tw \<and> inv_ncounter2 tw\<rbrace> next_counter \<lbrace>\<lambda>tw. inv_ncounter tw \<and> inv_ncounter2 tw\<rbrace>"
  apply (rule While_Suc)
  apply (rule Conseq'[where P="wp3_conc \<Gamma> next_counter (\<lambda>tw. inv_ncounter  (fst tw + 1, snd tw) \<and> 
                                                             inv_ncounter2 (fst tw + 1, snd tw))", rotated])
    apply (rule wp3_conc_is_pre, rule conc_stmt_wf_next_counter, rule nonneg_delay_conc_next_counter, rule cwt_ncnt, simp)
  unfolding next_counter_def wp3_conc_single'[OF cwt_ncnt[unfolded next_counter_def] nonneg_delay_conc_next_counter[unfolded next_counter_def]] wp3_fun.simps 
  apply (rule, rule, unfold if_bool_eq_conj, rule, rule) 
  apply (rule_tac[2] impI | rule_tac[2] conjI)+  apply (rule_tac[4] impI | rule_tac[4] conjI)+
  apply (rule_tac[6] impI | rule_tac[6] conjI)+  apply (rule_tac[8] impI | rule_tac[8] conjI)+
  apply (rule_tac[10] impI | rule_tac[10] conjI)+   apply (rule_tac[12] impI | rule_tac[12] conjI)+
  apply (rule_tac[14] impI | rule_tac[14] conjI)+
  subgoal using inv_ncounter_preserved inv_ncounter2_preserved by auto subgoal by auto
  subgoal unfolding fst_worldline_upd2 using inv_ncounter2 inv_ncounter_vwait_true by auto subgoal by auto
  subgoal using inv_ncounter2 inv_ncounter_vwait_false by auto subgoal by auto
  subgoal using inv_ncounter2 inv_ncounter_vpre by auto subgoal by auto
  subgoal using inv_ncounter2 inv_ncounter_vproc_true by auto subgoal by auto
  subgoal using inv_ncounter2 inv_ncounter_vproc_false by auto subgoal by auto
  subgoal using inv_ncounter2 inv_ncounter_vinit by auto subgoal by auto
  subgoal using inv_ncounter2 inv_ncounter_others by auto
  done

lemma init_ensures_ncounter:
  "init_sim2_hoare_wt \<Gamma> (\<lambda>tw. fst tw = 0) next_counter (\<lambda>tw. inv_ncounter tw \<and> inv_ncounter2 tw)"
  unfolding next_counter_def
  apply (rule AssignI_suc, rule SingleI)
  apply (rule Conseq3[where Q="\<lambda>tw. inv_ncounter (fst tw + 1, snd tw) \<and> inv_ncounter2 (fst tw + 1, snd tw)", rotated])
  apply (rule wp3_fun_is_pre[OF seq_wt_next_counter[unfolded next_counter_def conc_stmt.sel(4)] nonneg_delay_next_counter[unfolded next_counter_def conc_stmt.sel(4)]], simp)
  apply (rule, rule, unfold wp3_fun.simps(4), unfold if_bool_eq_conj)
  apply (rule conjI, rule impI)+
  apply (rule_tac[2] conjI | rule_tac[2] impI)+ apply (rule_tac[3] conjI | rule_tac[3] impI)+
  apply (rule_tac[4] conjI | rule_tac[4] impI)+ apply (rule_tac[5] conjI | rule_tac[5] impI)+
  subgoal using inv_ncounter2 inv_ncounter_vwait_true inv_ncounter_vwait_false unfolding wp3_fun.simps
    by (metis comp_apply eval_world_raw.simps(10) eval_world_raw.simps(21))
  subgoal using inv_ncounter2 inv_ncounter_vpre unfolding wp3_fun.simps
    by (metis comp_apply eval_world_raw.simps(10) eval_world_raw.simps(21))
  subgoal using inv_ncounter2 inv_ncounter_vproc_true inv_ncounter_vproc_false unfolding wp3_fun.simps
    by (metis comp_apply eval_world_raw.simps(10) eval_world_raw.simps(21))
  subgoal using inv_ncounter2 inv_ncounter_vinit unfolding wp3_fun.simps
    by (metis comp_apply eval_world_raw.simps(10) eval_world_raw.simps(21))
  subgoal using inv_ncounter2 inv_ncounter_others unfolding wp3_fun.simps
    by (metis eval_world_raw.simps(10) eval_world_raw.simps(21))
  done

lemma 
  assumes "sim_fin2 w (i + 1) next_counter tw'" and "wityping \<Gamma> w"
  shows "inv_ncounter tw'"
  using grand_correctness[OF assms conc_stmt_wf_next_counter cwt_ncnt nonneg_delay_conc_next_counter correctness_ncounter init_ensures_ncounter]
  by auto    
  
section \<open>Functional specification for @{term "next_accum"}\<close>  
                                                   
definition inv_naccum :: "sig assn2" where
  "inv_naccum tw = (bin_of NEXT_ACCUM at_time fst tw on tw = 
                   (case wline_of tw STATE (fst tw - 1) of    
                       V_PRE  \<Rightarrow> 0  |
                       V_PROC \<Rightarrow> sbintrunc 31 (sbl_to_bin (lval_of (value_of FRAC at_time fst tw - 1 on tw)) + 
                                              (sbl_to_bin (nths (lof_wline tw TERM1 (fst tw - 1)) {1 .. 32}))   ) |
                       V_INIT \<Rightarrow> 0 |
                       _      \<Rightarrow>   bin_of ACCUM at_time fst tw - 1 on tw 
                      ))"

definition inv_naccum2 :: "sig assn2" where
  "inv_naccum2 tw \<equiv> disjnt {STATE, ACCUM, FRAC, TERM1} (event_of tw) \<longrightarrow> 
                          (\<forall>i > fst tw. wline_of tw NEXT_ACCUM i = wline_of tw NEXT_ACCUM (fst tw))"

lemma inv_naccum2_preserved:
  "\<And>tw. inv_naccum2 tw \<and> (disjnt {STATE, ACCUM, FRAC, TERM1} (event_of tw)) \<Longrightarrow> inv_naccum2 (fst tw + 1, snd tw)"
  unfolding inv_naccum2_def by auto

lemma inv_naccum_preserved:
  "\<And>tw. inv_naccum tw \<and> inv_naccum2 tw \<and>  (disjnt {STATE, ACCUM, FRAC, TERM1} (event_of tw)) \<Longrightarrow> inv_naccum (fst tw + 1, snd tw)"
proof -
  fix tw
  assume *: "inv_naccum tw \<and> inv_naccum2 tw \<and> (disjnt {STATE, ACCUM, FRAC, TERM1} (event_of tw))"
  hence 0: "value_of ACCUM at_time (fst tw - 1) on tw = curr_value_of ACCUM on tw" and
        1: "value_of TERM1 at_time (fst tw - 1) on tw = curr_value_of TERM1 on tw" and
        2: "value_of FRAC at_time (fst tw - 1) on tw = curr_value_of FRAC on tw" and
        3: "value_of STATE at_time (fst tw - 1) on tw = curr_value_of STATE on tw"
    unfolding event_of_alt_def
    by (smt diff_0_eq_0 disjnt_insert1 mem_Collect_eq)+ 

  have  "inv_naccum tw" and "inv_naccum2 tw" and "(disjnt {STATE, ACCUM, FRAC, TERM1} (event_of tw))"
    using * by auto
  hence "bin_of NEXT_ACCUM at_time fst tw + 1 on tw = bin_of NEXT_ACCUM at_time fst tw on tw"
    unfolding inv_naccum2_def by auto
  also have "... = (case wline_of tw STATE (fst tw - 1) of    
                       V_PRE  \<Rightarrow> 0  |
                       V_PROC \<Rightarrow> sbintrunc 31 (sbl_to_bin (lval_of (value_of FRAC at_time fst tw - 1 on tw)) + 
                                              (sbl_to_bin (nths (lof_wline tw TERM1 (fst tw - 1)) {1 .. 32}))   ) |
                       V_INIT \<Rightarrow> 0 |
                       _      \<Rightarrow>   bin_of ACCUM at_time fst tw - 1 on tw 
                      )"
    using `inv_naccum tw` unfolding inv_naccum_def by auto
  also have "... = (case wline_of tw STATE (fst tw) of    
                       V_PRE  \<Rightarrow> 0  |
                       V_PROC \<Rightarrow> sbintrunc 31 (sbl_to_bin (lval_of (value_of FRAC at_time fst tw on tw)) + 
                                              (sbl_to_bin (nths (lof_wline tw TERM1 (fst tw)) {1 .. 32}))   ) |
                       V_INIT \<Rightarrow> 0 |
                       _      \<Rightarrow>   bin_of ACCUM at_time fst tw - 1 on tw 
                      )"
    unfolding 1 2 3 by auto
  finally show "inv_naccum (fst tw + 1, snd tw)"
    using 0 unfolding inv_naccum_def by (simp_all split: val.splits signedness.splits list.splits bool.splits)
qed

lemma inv_naccum_vpre:
  fixes tw
  assumes " curr_value_of STATE on tw = V_PRE"
  defines "tw' \<equiv> tw[ NEXT_ACCUM, 1 :=\<^sub>2 V_ZERO32]"
  assumes "wityping \<Gamma> (snd tw)"
  shows   "inv_naccum (fst tw' + 1, snd tw')"
proof -
  have "bin_of NEXT_ACCUM at_time fst tw' + 1 on (fst tw' + 1, snd tw') = bin_of NEXT_ACCUM at_time fst tw + 1 on tw'"
    unfolding tw'_def worldline_upd2_def worldline_upd_def by auto
  also have "... = 0"
    unfolding tw'_def worldline_upd2_def worldline_upd_def by auto
  also have "... = (case wline_of tw STATE (fst tw) of    
                       V_PRE  \<Rightarrow> 0  |
                       V_PROC \<Rightarrow> sbintrunc 31 (sbl_to_bin (lval_of (value_of FRAC at_time fst tw on tw)) + 
                                              (sbl_to_bin (nths (lof_wline tw TERM1 (fst tw)) {1 .. 32}))   ) |
                       V_INIT \<Rightarrow> 0 |
                       _      \<Rightarrow>   bin_of ACCUM at_time fst tw - 1 on tw 
                      )"
    using assms(1) by auto
  finally show ?thesis
    using assms(1)
    unfolding inv_naccum_def fst_conv comp_def snd_conv tw'_def worldline_upd2_def worldline_upd_def
    by (simp_all split: val.splits signedness.splits list.splits)
qed

lemma inv_naccum_vproc:
  fixes tw
  assumes " curr_value_of STATE on tw = V_PROC"
  defines "tw' \<equiv> tw[ NEXT_ACCUM, 1 :=\<^sub>2 eval_world_raw2 tw (Badd (Bsig FRAC) (Bslice TERM1 62 31))]"
  assumes "wityping \<Gamma> (snd tw)"
  shows   "inv_naccum (fst tw' + 1, snd tw')"
proof -
  have *: "snd (snd tw') STATE (get_time tw') = V_PROC"
    using assms(1) unfolding tw'_def worldline_upd2_def worldline_upd_def by auto
  have **: "snd (snd tw') FRAC (get_time tw') = snd (snd tw) FRAC (fst tw)"
    unfolding tw'_def worldline_upd2_def worldline_upd_def by auto
  have ***: "snd (snd tw') TERM1 (get_time tw') = snd (snd tw) TERM1 (get_time tw)"
    unfolding tw'_def worldline_upd2_def worldline_upd_def by auto
  have tyfrac: "type_of (snd (snd tw) FRAC (get_time tw)) = Lty Sig 32"
    using assms(3) cosine_locale_axioms unfolding cosine_locale_def wityping_def wtyping_def
    by auto
  have tyterm : "type_of (snd (snd tw) TERM1 (get_time tw)) = Lty Sig 64"
    using assms(3) cosine_locale_axioms unfolding cosine_locale_def wityping_def wtyping_def
    by auto
  hence len: "length (lval_of (wline_of tw TERM1 (get_time tw))) = 64"
    using `wityping \<Gamma> (snd tw)`  by (metis comp_apply ty.distinct(1) ty.inject type_of.elims val.sel(3))
  have len': "(length (nths (lval_of (curr_value_of TERM1 on tw)) {Suc 0..32})) = 32"
    unfolding length_nths len using card_slice[of "62" "64" "31"] by auto
  have "bin_of NEXT_ACCUM at_time fst tw' + 1 on (fst tw' + 1, snd tw') = bin_of NEXT_ACCUM at_time fst tw + 1 on tw'"
    unfolding tw'_def worldline_upd2_def worldline_upd_def by auto
  also have "... =  sbl_to_bin (bin_to_bl 32  (bin_of FRAC at_time fst tw on tw
                                                  +
                                               sbl_to_bin (nths (lval_of (curr_value_of TERM1 on tw)) {Suc 0..32})))"
    using tyterm tyfrac len' unfolding tw'_def worldline_upd2_def worldline_upd_def
    by (auto split:val.splits signedness.splits simp del: bin_to_bl_def)
  also have "... = sbintrunc 31 (bin_of FRAC at_time fst tw on tw
                                                  +
                                 sbl_to_bin (nths (lval_of (curr_value_of TERM1 on tw)) {Suc 0..32}))"
    using sbin_bl_bin_sbintruc by auto
  also have "... = (case wline_of tw STATE (fst tw) of    
                       V_PRE  \<Rightarrow> 0  |
                       V_PROC \<Rightarrow> sbintrunc 31 (sbl_to_bin (lval_of (value_of FRAC at_time fst tw on tw)) + 
                                              (sbl_to_bin (nths (lof_wline tw TERM1 (fst tw)) {1 .. 32}))   ) |
                       V_INIT \<Rightarrow> 0 |
                       _      \<Rightarrow>   bin_of ACCUM at_time fst tw - 1 on tw 
                      )"
    using assms(1) unfolding comp_def by auto
  finally show ?thesis
    using * assms(1) ** ***
    unfolding inv_naccum_def fst_conv comp_def snd_conv by (simp_all split: val.splits)
qed

lemma inv_naccum_vinit:
  fixes tw
  assumes " curr_value_of STATE on tw = V_INIT"
  defines "tw' \<equiv> tw[ NEXT_ACCUM, 1 :=\<^sub>2 V_ZERO32]"
  assumes "wityping \<Gamma> (snd tw)"
  shows   "inv_naccum (fst tw' + 1, snd tw')"
proof -
  have *: "snd (snd tw') STATE (get_time tw') = V_INIT"
    using assms(1) unfolding tw'_def worldline_upd2_def worldline_upd_def by auto
  have "bin_of NEXT_ACCUM at_time fst tw' + 1 on (fst tw' + 1, snd tw') = bin_of NEXT_ACCUM at_time fst tw + 1 on tw'"
    unfolding tw'_def worldline_upd2_def worldline_upd_def by auto
  also have "... = 0"
    unfolding tw'_def worldline_upd2_def worldline_upd_def by auto
  also have "... = (case wline_of tw STATE (fst tw) of    
                       V_PRE  \<Rightarrow> 0  |
                       V_PROC \<Rightarrow> sbintrunc 31 (sbl_to_bin (lval_of (value_of FRAC at_time fst tw on tw)) + 
                                              (sbl_to_bin (nths (lof_wline tw TERM1 (fst tw)) {1 .. 32}))   ) |
                       V_INIT \<Rightarrow> 0 |
                       _      \<Rightarrow>   bin_of ACCUM at_time fst tw - 1 on tw 
                      )"
    using assms(1) by auto
  finally show ?thesis
    using assms(1) *
    unfolding inv_naccum_def fst_conv comp_def snd_conv by (auto split:val.splits)
qed

lemma inv_naccum_others:
  fixes tw
  assumes " curr_value_of STATE on tw \<noteq> V_PRE"
  assumes " curr_value_of STATE on tw \<noteq> V_PROC"
  assumes " curr_value_of STATE on tw \<noteq> V_INIT"
  defines "tw' \<equiv> tw[ NEXT_ACCUM, 1 :=\<^sub>2 eval_world_raw2 tw (Bsig ACCUM)]"
  assumes "wityping \<Gamma> (snd tw)"
  shows   "inv_naccum (fst tw' + 1, snd tw')"
proof -
  have "bin_of NEXT_ACCUM at_time fst tw' + 1 on (fst tw' + 1, snd tw') = bin_of NEXT_ACCUM at_time fst tw + 1 on tw'"
    unfolding tw'_def worldline_upd2_def worldline_upd_def by auto
  also have "... = bin_of ACCUM at_time fst tw on tw"
    unfolding tw'_def worldline_upd2_def worldline_upd_def by auto
  also have "... = (case wline_of tw STATE (fst tw) of    
                       V_PRE  \<Rightarrow> 0  |
                       V_PROC \<Rightarrow> sbintrunc 31 (sbl_to_bin (lval_of (value_of FRAC at_time fst tw on tw)) + 
                                              (sbl_to_bin (nths (lof_wline tw TERM1 (fst tw)) {1 .. 32}))   ) |
                       V_INIT \<Rightarrow> 0 |
                       _      \<Rightarrow>   bin_of ACCUM at_time fst tw on tw 
                      )"
    using assms(1-3) by (auto split: val.splits signedness.splits list.splits bool.splits)
  finally show ?thesis
    unfolding inv_naccum_def fst_conv comp_def snd_conv tw'_def worldline_upd2_def worldline_upd_def 
    by (simp_all split:val.splits signedness.splits list.splits bool.splits)
qed

lemma inv_naccum2: 
  fixes tw v
  defines "tw' \<equiv> tw[NEXT_ACCUM, 1 :=\<^sub>2 v]"
  shows   "inv_naccum2 (fst tw' + 1, snd tw')"
  unfolding inv_naccum2_def tw'_def worldline_upd2_def worldline_upd_def by auto

lemma correctness_naccum:
  "\<Gamma> \<turnstile>\<^sub>s \<lbrace>\<lambda>tw. inv_naccum tw \<and> inv_naccum2 tw\<rbrace> next_accum \<lbrace>\<lambda>tw. inv_naccum tw \<and> inv_naccum2 tw\<rbrace>"
  apply (rule While_Suc)
  apply (rule Conseq'[where P="wp3_conc \<Gamma> next_accum (\<lambda>tw. inv_naccum  (fst tw + 1, snd tw) \<and> 
                                                           inv_naccum2 (fst tw + 1, snd tw))", rotated])  
    apply (rule wp3_conc_is_pre, rule conc_stmt_wf_next_accum, rule nonneg_delay_conc_next_accum, rule cwt_na, simp)
  unfolding next_accum_def wp3_conc_single'[OF cwt_na[unfolded next_accum_def] nonneg_delay_conc_next_accum[unfolded next_accum_def]] wp3_fun.simps 
  apply (rule, rule, unfold if_bool_eq_conj, rule, rule)
  apply (rule_tac[2] impI | rule_tac[2] conjI)+  apply (rule_tac[4] impI | rule_tac[4] conjI)+
       apply (rule_tac[6] impI | rule_tac[6] conjI)+  apply (rule_tac[8] impI | rule_tac[8] conjI)+
  subgoal using inv_naccum_preserved inv_naccum2_preserved by auto subgoal by auto
  subgoal using inv_naccum2 inv_naccum_vpre by auto subgoal by auto
  subgoal using inv_naccum2 inv_naccum_vproc by auto subgoal by auto
  subgoal using inv_naccum2 inv_naccum_vinit by auto subgoal by auto
  subgoal using inv_naccum2 inv_naccum_others by auto
  done

lemma helper: "Lv Sig (to_bl (0 :: 32 word)) = V_ZERO32"
  by eval

lemma init_ensures_naccum:
  "init_sim2_hoare_wt \<Gamma> (\<lambda>tw. fst tw = 0) next_accum (\<lambda>tw. inv_naccum tw \<and> inv_naccum2 tw)"
  unfolding next_accum_def
  apply (rule AssignI_suc, rule SingleI)
  apply (rule Conseq3[where Q="\<lambda>tw. inv_naccum (fst tw + 1, snd tw) \<and> inv_naccum2 (fst tw + 1, snd tw)", rotated])
  apply (rule wp3_fun_is_pre[OF seq_wt_next_accum[unfolded next_accum_def conc_stmt.sel(4)] nonneg_delay_next_accum[unfolded next_accum_def conc_stmt.sel(4)]], simp)
  apply (rule, rule, unfold wp3_fun.simps(4), unfold if_bool_eq_conj)
  apply (rule conjI, rule impI)+
  apply (rule_tac[2] impI | rule_tac[2] conjI)+  apply (rule_tac[3] impI | rule_tac[3] conjI)+ 
  apply (rule_tac[4] impI | rule_tac[4] conjI)+
  subgoal using inv_naccum2 inv_naccum_vpre unfolding wp3_fun.simps eval_world_raw.simps helper
    by (metis comp_apply eval_world_raw.simps(10) eval_world_raw.simps(21))
  subgoal using inv_naccum2 inv_naccum_vproc unfolding wp3_fun.simps 
    by (metis comp_apply eval_world_raw.simps(10) eval_world_raw.simps(21))
  subgoal using inv_naccum2 inv_naccum_vinit  unfolding wp3_fun.simps eval_world_raw.simps helper
    by (metis comp_apply eval_world_raw.simps(10))
  subgoal using inv_naccum2 inv_naccum_others unfolding wp3_fun.simps 
    by (metis comp_apply eval_world_raw.simps(10) eval_world_raw.simps(21))
  done

lemma 
  assumes "sim_fin2 w (i + 1) next_accum tw'" and "wityping \<Gamma> w"
  shows "inv_naccum tw'"
  using grand_correctness[OF assms conc_stmt_wf_next_accum cwt_na nonneg_delay_conc_next_accum correctness_naccum init_ensures_naccum]
  by auto    

section \<open>Functional specification of @{term "term1"}\<close>

definition inv_term1 :: "sig assn2" where
  "inv_term1 tw = (bin_of TERM1 at_time fst tw on tw = sbintrunc 63 ((bin_of COMMON at_time fst tw - 1 on tw) * (bin_of ACCUM at_time fst tw - 1 on tw)))"

definition inv_term12 :: "sig assn2" where
  "inv_term12 tw \<equiv> disjnt {COMMON, ACCUM} (event_of tw) \<longrightarrow> (\<forall>i > fst tw. bin_of TERM1 at_time i on tw = bin_of TERM1 at_time fst tw on tw)"

lemma inv_term12_preserved:
  "\<And>tw. inv_term12 tw \<and> (disjnt {COMMON, ACCUM} (event_of tw)) \<Longrightarrow> inv_term12 (fst tw + 1, snd tw)"
  unfolding inv_term12_def by auto

lemma inv_term1_preserved:
  "\<And>tw. inv_term1 tw \<and> inv_term12 tw \<and>  (disjnt {COMMON, ACCUM} (event_of tw)) \<Longrightarrow> inv_term1 (fst tw + 1, snd tw)"
proof -
  fix tw 
  assume "inv_term1 tw \<and> inv_term12 tw \<and>  (disjnt {COMMON, ACCUM} (event_of tw)) "
  hence "inv_term1 tw" and "inv_term12 tw" and "disjnt {COMMON, ACCUM} (event_of tw)"
    by auto
  hence "bin_of TERM1 at_time fst tw + 1 on tw = bin_of TERM1 at_time fst tw on tw"
    unfolding inv_term12_def by auto
  also have "... = sbintrunc 63 ((bin_of COMMON at_time fst tw - 1 on tw) * (bin_of ACCUM at_time fst tw - 1 on tw))"
    using `inv_term1 tw` unfolding inv_term1_def by auto
  also have "... = sbintrunc 63 ((bin_of COMMON at_time fst tw on tw) * (bin_of ACCUM at_time fst tw on tw))"
    using `disjnt {COMMON, ACCUM} (event_of tw)` unfolding event_of_alt_def 
    by (smt disjnt_insert1 mem_Collect_eq minus_eq)
  finally show "inv_term1 (fst tw + 1, snd tw)"
    unfolding inv_term1_def by auto
qed

lemma inv_term1_next_time:
  fixes tw
  defines "v \<equiv> eval_world_raw2 tw (Bmult (Bsig COMMON) (Bsig ACCUM))"
  defines "tw' \<equiv> tw[TERM1 , 1 :=\<^sub>2 v]"
  assumes "wityping \<Gamma> (snd tw)"
  shows   "inv_term1 (fst tw' + 1, snd tw')"
proof -
  have *: "type_of (snd (snd tw) COMMON (fst tw)) = Lty Sig 32"
    using cosine_locale_axioms `wityping \<Gamma> (snd tw)` 
    unfolding wityping_def wtyping_def cosine_locale_def by auto
  have **: "type_of (snd (snd tw) ACCUM (fst tw)) = Lty Sig 32"
    using cosine_locale_axioms `wityping \<Gamma> (snd tw)` 
    unfolding wityping_def wtyping_def cosine_locale_def by auto
  have "bin_of TERM1 at_time fst tw' + 1 on (fst tw' + 1, snd tw') = bin_of TERM1 at_time fst tw' + 1 on tw'"
    unfolding fst_conv comp_def tw'_def worldline_upd2_def worldline_upd_def by auto
  also have "... = bin_of TERM1 at_time fst tw + 1 on tw'"
    unfolding tw'_def fst_worldline_upd2 by auto
  also have "... = sbl_to_bin (lval_of v)"
    unfolding tw'_def worldline_upd2_def worldline_upd_def by auto
  also have "... = sbl_to_bin (bin_to_bl 64 ((sbl_to_bin (lval_of (curr_value_of COMMON on tw))) * (sbl_to_bin (lval_of (curr_value_of ACCUM on tw)))))"
    using * ** unfolding v_def eval_world_raw.simps eval_arith.simps Let_def power_def by (auto split: val.splits)
  also have "... = sbintrunc 63 ((bin_of COMMON at_time fst tw on tw) * (bin_of ACCUM at_time fst tw on tw))"
    using sbin_bl_bin_sbintruc by auto
  also have "... = sbintrunc 63 ((bin_of COMMON at_time fst tw' on (fst tw' + 1, snd tw')) * (bin_of ACCUM at_time fst tw' on (fst tw' + 1, snd tw')))"
    unfolding tw'_def fst_worldline_upd2 comp_def worldline_upd2_def worldline_upd_def by auto
  finally show ?thesis
    unfolding inv_term1_def by auto
qed

lemma inv_term12_next_time:
  fixes tw
  defines "v \<equiv> eval_world_raw2 tw (Bmult (Bsig COMMON) (Bsig ACCUM))"
  defines "tw' \<equiv> tw[TERM1 , 1 :=\<^sub>2 v]"
  shows   "inv_term12 (fst tw' + 1, snd tw')"
  using assms unfolding inv_term12_def tw'_def worldline_upd2_def worldline_upd_def by auto 
 
lemma correctness_term1:
  "\<Gamma> \<turnstile>\<^sub>s \<lbrace>\<lambda>tw. inv_term1 tw \<and> inv_term12 tw\<rbrace> term1 \<lbrace>\<lambda>tw. inv_term1 tw \<and> inv_term12 tw\<rbrace>"
  apply (rule While_Suc)
  apply (rule Conseq'[where P="wp3_conc \<Gamma> term1 (\<lambda>tw. inv_term1  (fst tw + 1, snd tw) \<and> 
                                                           inv_term12 (fst tw + 1, snd tw))", rotated])  
  apply (rule wp3_conc_is_pre, rule conc_stmt_wf_term1, rule nonneg_delay_conc_term1, rule cwt_t1, simp)
  unfolding term1_def wp3_conc_single'[OF cwt_t1[unfolded term1_def] nonneg_delay_conc_term1[unfolded term1_def]] wp3_fun.simps 
  apply (rule, rule, unfold if_bool_eq_conj, rule, rule, rule_tac[2] impI) 
  subgoal using inv_term1_preserved inv_term12_preserved by auto  
  subgoal using inv_term1_next_time inv_term12_next_time by auto
  done

lemma init_ensures_term1:
  "init_sim2_hoare_wt \<Gamma> (\<lambda>tw. fst tw = 0) term1 (\<lambda>tw. inv_term1 tw \<and> inv_term12 tw)"
  unfolding term1_def
  apply (rule AssignI_suc, rule SingleI)
  apply (rule Conseq3[where Q="\<lambda>tw. inv_term1 (fst tw + 1, snd tw) \<and> inv_term12 (fst tw + 1, snd tw)", rotated])
  apply (rule wp3_fun_is_pre[OF seq_wt_term1[unfolded term1_def conc_stmt.sel(4)] nonneg_delay_term1[unfolded term1_def conc_stmt.sel(4)]], simp)
  apply (rule, rule, unfold wp3_fun.simps)
  using inv_term1_next_time inv_term12_next_time by blast

section \<open>Functional specification of @{term "next_frac"}\<close>

definition inv_nfrac :: "sig assn2" where
  "inv_nfrac tw \<equiv> ((bin_of NEXT_FRAC at_time fst tw on tw) = 
                      (case nat ubin_of COUNTER at_time fst tw - 1 on tw of 
                          0 \<Rightarrow> approx_one |
                          Suc 0 \<Rightarrow> approx_half |
                          Suc (Suc 0) \<Rightarrow> approx_fourth |
                          Suc (Suc (Suc 0)) \<Rightarrow> approx_sixth |
                          Suc (Suc (Suc (Suc 0))) \<Rightarrow> approx_eighth | 
                          _ \<Rightarrow> 0))"

definition inv_nfrac2 :: "sig assn2" where
  "inv_nfrac2 tw \<equiv> disjnt {COUNTER} (event_of tw) \<longrightarrow> (\<forall>i > fst tw. bin_of NEXT_FRAC at_time i on tw = bin_of NEXT_FRAC at_time fst tw on tw)"

lemma inv_nfrac2_preserved:
  "\<And>tw. inv_nfrac2 tw \<and> (disjnt {COUNTER} (event_of tw)) \<Longrightarrow> inv_nfrac2 (fst tw + 1, snd tw)"
  unfolding inv_nfrac2_def by auto

lemma inv_nfrac_preserved:
  "\<And>tw. inv_nfrac tw \<and> inv_nfrac2 tw \<and>  (disjnt {COUNTER} (event_of tw)) \<Longrightarrow> inv_nfrac (fst tw + 1, snd tw)"
proof -
  fix tw 
  assume "inv_nfrac tw \<and> inv_nfrac2 tw \<and>  (disjnt {COUNTER} (event_of tw)) "
  hence "inv_nfrac tw" and "inv_nfrac2 tw" and "disjnt {COUNTER} (event_of tw)"
    by auto
  hence "bin_of NEXT_FRAC at_time fst tw + 1 on tw = bin_of NEXT_FRAC at_time fst tw on tw"
    unfolding inv_nfrac2_def by auto
  also have "... = (case nat ubin_of COUNTER at_time fst tw - 1 on tw of 
                          0 \<Rightarrow> approx_one |
                          Suc 0 \<Rightarrow> approx_half |
                          Suc (Suc 0) \<Rightarrow> approx_fourth |
                          Suc (Suc (Suc 0)) \<Rightarrow> approx_sixth |
                          Suc (Suc (Suc (Suc 0))) \<Rightarrow> approx_eighth | _ \<Rightarrow> 0)"
    using `inv_nfrac tw` unfolding inv_nfrac_def by auto
  also have "... = (case nat ubin_of COUNTER at_time fst tw on tw of 
                          0 \<Rightarrow> approx_one |
                          Suc 0 \<Rightarrow> approx_half |
                          Suc (Suc 0) \<Rightarrow> approx_fourth |
                          Suc (Suc (Suc 0)) \<Rightarrow> approx_sixth |
                          Suc (Suc (Suc (Suc 0))) \<Rightarrow> approx_eighth | _ \<Rightarrow> 0)"
    using `disjnt {COUNTER} (event_of tw)` unfolding event_of_alt_def 
    by (smt disjnt_insert1 mem_Collect_eq minus_eq)
  finally show "inv_nfrac (fst tw + 1, snd tw)"
    unfolding inv_nfrac_def by auto
qed


lemma inv_nfrac_4:
  fixes tw
  assumes " curr_value_of COUNTER on tw = V_4"
  defines "tw' \<equiv> tw[ NEXT_FRAC, 1 :=\<^sub>2  Lv Sig (to_bl (approx_eighth :: 32 word))]"
  assumes "wityping \<Gamma> (snd tw)"
  shows   "inv_nfrac (fst tw' + 1, snd tw')"
proof -
  have *: "nat (bl_to_bin [True, False, False]) = 4"
    by eval
  have "bin_of NEXT_FRAC at_time fst tw' + 1 on (fst tw' + 1, snd tw') = bin_of NEXT_FRAC at_time fst tw + 1 on tw'"
    unfolding tw'_def worldline_upd2_def worldline_upd_def by auto
  also have "... = sint (approx_eighth :: 32 word)"
    unfolding tw'_def worldline_upd2_def worldline_upd_def using sbl_to_bin_to_bl
    by auto
  also have "... = (approx_eighth :: int)"
    by eval
  also have "... = (case nat ubin_of COUNTER at_time fst tw on tw of 
                          0 \<Rightarrow> approx_one |
                          Suc 0 \<Rightarrow> approx_half |
                          Suc (Suc 0) \<Rightarrow> approx_fourth |
                          Suc (Suc (Suc 0)) \<Rightarrow> approx_sixth |
                          Suc (Suc (Suc (Suc 0))) \<Rightarrow> approx_eighth | _ \<Rightarrow> 0)"
    using assms(1) * by auto
  finally show ?thesis
    unfolding inv_nfrac_def fst_conv comp_def snd_conv tw'_def
    worldline_upd2_def worldline_upd_def by (auto)
qed

lemma inv_nfrac_3:
  fixes tw
  assumes " curr_value_of COUNTER on tw = V_3"
  defines "tw' \<equiv> tw[ NEXT_FRAC, 1 :=\<^sub>2  Lv Sig (to_bl (approx_sixth :: 32 word))]"
  assumes "wityping \<Gamma> (snd tw)"
  shows   "inv_nfrac (fst tw' + 1, snd tw')"
proof -
  have *: "nat (bl_to_bin [False, True, True]) = 3"
    by eval
  have "bin_of NEXT_FRAC at_time fst tw' + 1 on (fst tw' + 1, snd tw') = bin_of NEXT_FRAC at_time fst tw + 1 on tw'"
    unfolding tw'_def worldline_upd2_def worldline_upd_def by auto
  also have "... = sint (approx_sixth :: 32 word)"
    unfolding tw'_def worldline_upd2_def worldline_upd_def using sbl_to_bin_to_bl
    by auto
  also have "... = (approx_sixth :: int)"
    by eval
  also have "... = (case nat ubin_of COUNTER at_time fst tw on tw of 
                          0 \<Rightarrow> approx_one |
                          Suc 0 \<Rightarrow> approx_half |
                          Suc (Suc 0) \<Rightarrow> approx_fourth |
                          Suc (Suc (Suc 0)) \<Rightarrow> approx_sixth |
                          Suc (Suc (Suc (Suc 0))) \<Rightarrow> approx_eighth | _ \<Rightarrow> 0)"
    using assms(1) * by auto
  finally show ?thesis
    unfolding inv_nfrac_def fst_conv comp_def snd_conv tw'_def
    worldline_upd2_def worldline_upd_def by (auto)
qed

lemma inv_nfrac_2:
  fixes tw
  assumes " curr_value_of COUNTER on tw = V_2"
  defines "tw' \<equiv> tw[ NEXT_FRAC, 1 :=\<^sub>2  Lv Sig (to_bl (approx_fourth :: 32 word))]"
  assumes "wityping \<Gamma> (snd tw)"
  shows   "inv_nfrac (fst tw' + 1, snd tw')"
proof -
  have *: "nat (bl_to_bin [False, True, False]) = 2"
    by eval
  have "bin_of NEXT_FRAC at_time fst tw' + 1 on (fst tw' + 1, snd tw') = bin_of NEXT_FRAC at_time fst tw + 1 on tw'"
    unfolding tw'_def worldline_upd2_def worldline_upd_def by auto
  also have "... = sint (approx_fourth :: 32 word)"
    unfolding tw'_def worldline_upd2_def worldline_upd_def using sbl_to_bin_to_bl
    by auto
  also have "... = (approx_fourth :: int)"
    by eval
  also have "... = (case nat ubin_of COUNTER at_time fst tw on tw of 
                          0 \<Rightarrow> approx_one |
                          Suc 0 \<Rightarrow> approx_half |
                          Suc (Suc 0) \<Rightarrow> approx_fourth |
                          Suc (Suc (Suc 0)) \<Rightarrow> approx_sixth |
                          Suc (Suc (Suc (Suc 0))) \<Rightarrow> approx_eighth | _ \<Rightarrow> 0)"
    using assms(1) * by auto
  finally show ?thesis
    unfolding inv_nfrac_def fst_conv comp_def snd_conv tw'_def
    worldline_upd2_def worldline_upd_def by (auto)
qed

lemma inv_nfrac_1:
  fixes tw
  assumes " curr_value_of COUNTER on tw = V_1"
  defines "tw' \<equiv> tw[ NEXT_FRAC, 1 :=\<^sub>2  Lv Sig (to_bl (approx_half :: 32 word))]"
  assumes "wityping \<Gamma> (snd tw)"
  shows   "inv_nfrac (fst tw' + 1, snd tw')"
proof -
  have *: "nat (bl_to_bin [False, False, True]) = 1"
    by eval
  have "bin_of NEXT_FRAC at_time fst tw' + 1 on (fst tw' + 1, snd tw') = bin_of NEXT_FRAC at_time fst tw + 1 on tw'"
    unfolding tw'_def worldline_upd2_def worldline_upd_def by auto
  also have "... = sint (approx_half :: 32 word)"
    unfolding tw'_def worldline_upd2_def worldline_upd_def using sbl_to_bin_to_bl
    by auto
  also have "... = (approx_half :: int)"
    by eval
  also have "... = (case nat ubin_of COUNTER at_time fst tw on tw of 
                          0 \<Rightarrow> approx_one |
                          Suc 0 \<Rightarrow> approx_half |
                          Suc (Suc 0) \<Rightarrow> approx_fourth |
                          Suc (Suc (Suc 0)) \<Rightarrow> approx_sixth |
                          Suc (Suc (Suc (Suc 0))) \<Rightarrow> approx_eighth | _ \<Rightarrow> 0)"
    using assms(1) * by auto
  finally show ?thesis
    unfolding inv_nfrac_def fst_conv comp_def snd_conv tw'_def
    worldline_upd2_def worldline_upd_def by (auto)
qed

lemma inv_nfrac_0:
  fixes tw
  assumes " curr_value_of COUNTER on tw = V_0"
  defines "tw' \<equiv> tw[ NEXT_FRAC, 1 :=\<^sub>2  Lv Sig (to_bl (approx_one :: 32 word))]"
  assumes "wityping \<Gamma> (snd tw)"
  shows   "inv_nfrac (fst tw' + 1, snd tw')"
proof -
  have *: "nat (bl_to_bin [False, False, False]) = 0"
    by eval
  have "bin_of NEXT_FRAC at_time fst tw' + 1 on (fst tw' + 1, snd tw') = bin_of NEXT_FRAC at_time fst tw + 1 on tw'"
    unfolding tw'_def worldline_upd2_def worldline_upd_def by auto
  also have "... = sint (approx_one :: 32 word)"
    unfolding tw'_def worldline_upd2_def worldline_upd_def using sbl_to_bin_to_bl
    by auto
  also have "... = (approx_one :: int)"
    by eval
  also have "... = (case nat ubin_of COUNTER at_time fst tw on tw of 
                          0 \<Rightarrow> approx_one |
                          Suc 0 \<Rightarrow> approx_half |
                          Suc (Suc 0) \<Rightarrow> approx_fourth |
                          Suc (Suc (Suc 0)) \<Rightarrow> approx_sixth |
                          Suc (Suc (Suc (Suc 0))) \<Rightarrow> approx_eighth | _ \<Rightarrow> 0)"
    using assms(1) * by auto
  finally show ?thesis
    unfolding inv_nfrac_def fst_conv comp_def snd_conv tw'_def
    worldline_upd2_def worldline_upd_def by (auto)
qed

lemma inv_nfrac_others:
  fixes tw
  assumes " curr_value_of COUNTER on tw \<noteq> Lv Uns (to_bl (0 :: 3 word))"
  assumes " curr_value_of COUNTER on tw \<noteq> Lv Uns (to_bl (1 :: 3 word))"
  assumes " curr_value_of COUNTER on tw \<noteq> Lv Uns (to_bl (2 :: 3 word))"
  assumes " curr_value_of COUNTER on tw \<noteq> Lv Uns (to_bl (3 :: 3 word))"
  assumes " curr_value_of COUNTER on tw \<noteq> Lv Uns (to_bl (4 :: 3 word))"
  defines "tw' \<equiv> tw[ NEXT_FRAC, 1 :=\<^sub>2  Lv Sig (to_bl (0 :: 32 word))]"
  assumes "wityping \<Gamma> (snd tw)"
  shows   "inv_nfrac (fst tw' + 1, snd tw')"
proof -
  have "type_of (snd (snd tw) COUNTER (fst tw)) = Lty Uns 3"
    using `wityping \<Gamma> (snd tw)` cosine_locale_axioms unfolding wityping_def wtyping_def cosine_locale_def
    by auto
  then obtain bs where counter_is: " snd (snd tw) COUNTER (fst tw) = Lv Uns bs" and "length bs = 3"
    by (metis ty.distinct(1) ty.inject type_of.elims)
  have 0: "nat (bl_to_bin bs) \<noteq>  0"
  proof (rule ccontr)
    assume "\<not> nat (bl_to_bin bs) \<noteq>  0" hence "nat (bl_to_bin bs) = 0"
      by auto
    moreover have "nat (bl_to_bin bs) = bl_to_bin bs"
      using bl_to_bin_ge0 by auto
    ultimately have "bl_to_bin bs = 0"
      by auto
    hence "bin_to_bl (length bs) (bl_to_bin bs) = bin_to_bl 3 0"
      using `length bs = 3` by auto
    also have "... = [False, False, False]"
      by eval
    finally have "bs = [False, False, False]"
      unfolding bl_bin_bl by auto
    with assms(1) show False
      using counter_is unfolding comp_def by auto
  qed
  have 1: "nat (bl_to_bin bs) \<noteq> Suc 0"
  proof (rule ccontr)
    assume "\<not> nat (bl_to_bin bs) \<noteq> Suc 0" hence "nat (bl_to_bin bs) = Suc 0"
      by auto
    moreover have "nat (bl_to_bin bs) = bl_to_bin bs"
      using bl_to_bin_ge0 by auto
    ultimately have "bl_to_bin bs = 1"
      by auto
    hence "bin_to_bl (length bs) (bl_to_bin bs) = bin_to_bl 3 1"
      using `length bs = 3` by auto
    also have "... = [False, False, True]"
      by eval
    finally have "bs = [False, False, True]"
      unfolding bl_bin_bl by auto
    moreover have "to_bl (1 :: 3 word) = [False, False, True]"
      by eval
    ultimately show False
      using assms(2) counter_is unfolding comp_def by auto
  qed
  have 2: "nat (bl_to_bin bs) \<noteq> Suc (Suc 0)"
  proof (rule ccontr)
    assume "\<not> nat (bl_to_bin bs) \<noteq> Suc (Suc 0)" hence "nat (bl_to_bin bs) = Suc (Suc 0)"
      by auto
    moreover have "nat (bl_to_bin bs) = bl_to_bin bs"
      using bl_to_bin_ge0 by auto
    ultimately have "bl_to_bin bs = 2"
      by auto
    hence "bin_to_bl (length bs) (bl_to_bin bs) = bin_to_bl 3 2"
      using `length bs = 3` by auto
    also have "... = [False, True, False]"
      by eval
    finally have "bs = [False, True, False]"
      unfolding bl_bin_bl by auto
    with assms(3) show False
      using counter_is unfolding comp_def by auto
  qed
  have 3: "nat (bl_to_bin bs) \<noteq> Suc (Suc (Suc 0))"
  proof (rule ccontr)
    assume "\<not> nat (bl_to_bin bs) \<noteq> Suc (Suc (Suc 0))" hence "nat (bl_to_bin bs) = Suc (Suc (Suc 0))"
      by auto
    moreover have "nat (bl_to_bin bs) = bl_to_bin bs"
      using bl_to_bin_ge0 by auto
    ultimately have "bl_to_bin bs = 3"
      by auto
    hence "bin_to_bl (length bs) (bl_to_bin bs) = bin_to_bl 3 3"
      using `length bs = 3` by auto
    also have "... = [False, True, True]"
      by eval
    finally have "bs = [False, True, True]"
      unfolding bl_bin_bl by auto
    with assms(4) show False
      using counter_is unfolding comp_def by auto
  qed
  have 4: "nat (bl_to_bin bs) \<noteq> Suc (Suc (Suc (Suc 0)))"
  proof (rule ccontr)
    assume "\<not> nat (bl_to_bin bs) \<noteq> Suc (Suc (Suc (Suc 0)))" hence "nat (bl_to_bin bs) = Suc (Suc (Suc (Suc 0)))"
      by auto
    moreover have "nat (bl_to_bin bs) = bl_to_bin bs"
      using bl_to_bin_ge0 by auto
    ultimately have "bl_to_bin bs = 4"
      by auto
    hence "bin_to_bl (length bs) (bl_to_bin bs) = bin_to_bl 3 4"
      using `length bs = 3` by auto
    also have "... = [True, False, False]"
      by eval
    finally have "bs = [True, False, False]"
      unfolding bl_bin_bl by auto
    with assms(5) show False
      using counter_is unfolding comp_def by auto
  qed
  have "bin_of NEXT_FRAC at_time fst tw' + 1 on (fst tw' + 1, snd tw') = bin_of NEXT_FRAC at_time fst tw + 1 on tw'"
    unfolding tw'_def worldline_upd2_def worldline_upd_def by auto
  also have "... = sint (0 :: 32 word)"
    unfolding tw'_def worldline_upd2_def worldline_upd_def using sbl_to_bin_to_bl
    by auto
  also have "... = (0 :: int)"
    by eval
  also have "... = (case nat ubin_of COUNTER at_time fst tw on tw of 
                          0 \<Rightarrow> approx_one |
                          Suc 0 \<Rightarrow> approx_half |
                          Suc (Suc 0) \<Rightarrow> approx_fourth |
                          Suc (Suc (Suc 0)) \<Rightarrow> approx_sixth |
                          Suc (Suc (Suc (Suc 0))) \<Rightarrow> approx_eighth | _ \<Rightarrow> 0)"
    using 0 1 2 3 4 counter_is by (auto split: nat.splits)
  finally show ?thesis
    unfolding inv_nfrac_def fst_conv comp_def snd_conv tw'_def
    worldline_upd2_def worldline_upd_def by (auto)
qed

lemma inv_nfrac2: 
  fixes tw v
  defines "tw' \<equiv> tw[NEXT_FRAC, 1 :=\<^sub>2 v]"
  shows   "inv_nfrac2 (fst tw' + 1, snd tw')"
  unfolding inv_nfrac2_def tw'_def worldline_upd2_def worldline_upd_def by auto

lemma correctness_nfrac:                          
  "\<Gamma> \<turnstile>\<^sub>s \<lbrace>\<lambda>tw. inv_nfrac tw \<and> inv_nfrac2 tw\<rbrace> next_frac \<lbrace>\<lambda>tw. inv_nfrac tw \<and> inv_nfrac2 tw\<rbrace>"
  apply (rule While_Suc)
  apply (rule Conseq'[where P="wp3_conc \<Gamma> next_frac (\<lambda>tw. inv_nfrac  (fst tw + 1, snd tw) \<and> 
                                                          inv_nfrac2 (fst tw + 1, snd tw))", rotated])  
  apply (rule wp3_conc_is_pre, rule conc_stmt_wf_next_frac, rule nonneg_delay_conc_next_frac, rule cwt_nf, simp)
  unfolding next_frac_def wp3_conc_single'[OF cwt_nf[unfolded next_frac_def] nonneg_delay_conc_next_frac[unfolded next_frac_def]] wp3_fun.simps 
  apply (rule, rule, unfold if_bool_eq_conj, rule, rule, rule_tac[2] impI) 
  apply (rule_tac[2] impI | rule_tac[2] conjI)+  apply (rule_tac[4] impI | rule_tac[4] conjI)+
  apply (rule_tac[6] impI | rule_tac[6] conjI)+  apply (rule_tac[8] impI | rule_tac[8] conjI)+
  apply (rule_tac[10] impI | rule_tac[10] conjI)+   
  subgoal using inv_nfrac_preserved inv_nfrac2_preserved by auto subgoal by auto
  subgoal using inv_nfrac2 inv_nfrac_4 by auto subgoal by auto
  subgoal using inv_nfrac2 inv_nfrac_3 by auto subgoal by auto
  subgoal using inv_nfrac2 inv_nfrac_2 by auto subgoal by auto
  subgoal 
  proof -
    fix tw
    assume *: "wityping \<Gamma> (snd tw) \<and> inv_nfrac tw \<and> inv_nfrac2 tw"
    assume "eval_world_raw2 tw (Bsig COUNTER) = eval_world_raw2 tw (Bliteral Uns (to_bl (1 :: 3 word)))"
    hence "snd (snd tw) COUNTER (get_time tw) = Lv Uns (to_bl (1 :: 3 word))"
      by auto
    also have "... = Lv Uns [False, False, True]"
      by eval
    finally have **: "curr_value_of COUNTER on tw = V_1"
      by auto
    hence "inv_nfrac
     (get_time tw[ NEXT_FRAC, 1 :=\<^sub>2 eval_world_raw2 tw (Bliteral Sig (to_bl (approx_half :: 32 word)))] + 1, snd tw[ NEXT_FRAC, 1 :=\<^sub>2 eval_world_raw2 tw (Bliteral Sig (to_bl (approx_half :: 32 word)))])"
      using inv_nfrac_1 * by auto
    moreover have "inv_nfrac2
     (get_time tw[ NEXT_FRAC, 1 :=\<^sub>2 eval_world_raw2 tw (Bliteral Sig (to_bl (approx_half :: 32 word)))] + 1, snd tw[ NEXT_FRAC, 1 :=\<^sub>2 eval_world_raw2 tw (Bliteral Sig (to_bl (approx_half :: 32 word)))])"
      using inv_nfrac2 by auto
    ultimately show " inv_nfrac
     (get_time tw[ NEXT_FRAC, 1 :=\<^sub>2 eval_world_raw2 tw (Bliteral Sig (to_bl (approx_half :: 32 word)))] + 1, snd tw[ NEXT_FRAC, 1 :=\<^sub>2 eval_world_raw2 tw (Bliteral Sig (to_bl (approx_half :: 32 word)))]) \<and>
    inv_nfrac2
     (get_time tw[ NEXT_FRAC, 1 :=\<^sub>2 eval_world_raw2 tw (Bliteral Sig (to_bl (approx_half :: 32 word)))] + 1, snd tw[ NEXT_FRAC, 1 :=\<^sub>2 eval_world_raw2 tw (Bliteral Sig (to_bl (approx_half :: 32 word)))])"
      by auto
  qed
  subgoal by auto
  subgoal using inv_nfrac2 inv_nfrac_0 by auto 
  subgoal using inv_nfrac_others inv_nfrac2 by auto
  done

lemma helper2: "Lv Uns (to_bl (4 :: 3 word)) = V_4"
  by eval

lemma helper3: "Lv Uns (to_bl (3 :: 3 word)) = V_3"
  by eval

lemma helper4: "Lv Uns (to_bl (2 :: 3 word)) = V_2"
  by eval

lemma helper5: "Lv Uns (to_bl (1 :: 3 word)) = V_1"
  by eval

lemma helper6: "Lv Uns (to_bl (0 :: 3 word)) = V_0"
  by eval

lemma init_ensures_nfrac:
  "init_sim2_hoare_wt \<Gamma> (\<lambda>tw. fst tw = 0) next_frac (\<lambda>tw. inv_nfrac tw \<and> inv_nfrac2 tw)"
  unfolding next_frac_def
  apply (rule AssignI_suc, rule SingleI)
  apply (rule Conseq3[where Q="\<lambda>tw. inv_nfrac (fst tw + 1, snd tw) \<and> inv_nfrac2 (fst tw + 1, snd tw)", rotated])
  apply (rule wp3_fun_is_pre[OF seq_wt_next_frac[unfolded next_frac_def conc_stmt.sel(4)] nonneg_delay_next_frac[unfolded next_frac_def conc_stmt.sel(4)]], simp)
  apply (rule, rule, unfold wp3_fun.simps(4), unfold if_bool_eq_conj)
  apply (rule conjI | rule impI)+
  apply (rule_tac[2] impI | rule_tac[2] conjI)+  apply (rule_tac[3] impI | rule_tac[3] conjI)+
     apply (rule_tac[4] impI | rule_tac[4] conjI)+  apply (rule_tac[5] impI | rule_tac[5] conjI)+
       apply (rule_tac[6] impI | rule_tac[6] conjI)+  
  subgoal unfolding wp3_fun.simps eval_world_raw.simps helper2 using inv_nfrac2 inv_nfrac_4 
    by (metis comp_apply eval_world_raw.simps(10))
  subgoal unfolding wp3_fun.simps eval_world_raw.simps helper3 using inv_nfrac2 inv_nfrac_3
    by (metis comp_apply eval_world_raw.simps(10))
  subgoal unfolding wp3_fun.simps eval_world_raw.simps helper4 using inv_nfrac2 inv_nfrac_2
    by (metis comp_apply eval_world_raw.simps(10))
  subgoal unfolding wp3_fun.simps eval_world_raw.simps helper5 using inv_nfrac2 inv_nfrac_1
    by (metis comp_apply eval_world_raw.simps(10))
  subgoal unfolding wp3_fun.simps eval_world_raw.simps helper6 using inv_nfrac2 inv_nfrac_0
    by (metis comp_apply eval_world_raw.simps(10))
  subgoal unfolding wp3_fun.simps eval_world_raw.simps using inv_nfrac2 inv_nfrac_others
    by (metis comp_apply eval_world_raw.simps(10))
  done
    
lemma 
  assumes "sim_fin2 w (i + 1) next_frac tw'" and "wityping \<Gamma> w"
  shows "inv_nfrac tw'"
  using grand_correctness[OF assms conc_stmt_wf_next_frac cwt_nf nonneg_delay_conc_next_frac correctness_nfrac init_ensures_nfrac]
  by auto  
                                           
section \<open>Functional specification of @{term "next_outready_reg"}\<close>

definition inv_nout :: "sig assn2" where
  "inv_nout tw = (bval_of (curr_value_of NEXT_OUTREADYREG on tw) = 
                  (case wline_of tw STATE (fst tw - 1) of    
                       V_PROC \<Rightarrow> \<not> bval_of (value_of CTR_NEQ_0 at_time fst tw - 1 on tw) |
                       V_POST \<Rightarrow> bval_of (value_of OUTREADY_REG at_time fst tw - 1 on tw) |
                       _      \<Rightarrow>   False))"

definition inv_nout2 :: "sig assn2" where
  "inv_nout2 tw \<equiv> disjnt {STATE, CTR_NEQ_0, OUTREADY_REG} (event_of tw) \<longrightarrow> 
          (\<forall>i > fst tw. bval_of (value_of NEXT_OUTREADYREG at_time i on tw) = bval_of (value_of NEXT_OUTREADYREG at_time fst tw on tw))"

lemma inv_nout2_preserved:
  "\<And>tw. inv_nout2 tw \<and> (disjnt {STATE, CTR_NEQ_0, OUTREADY_REG} (event_of tw)) \<Longrightarrow> inv_nout2 (fst tw + 1, snd tw)"
  unfolding inv_nout2_def by auto

lemma inv_nout_preserved:
  "\<And>tw. inv_nout tw \<and> inv_nout2 tw \<and>  (disjnt {STATE, CTR_NEQ_0, OUTREADY_REG} (event_of tw)) \<Longrightarrow> inv_nout (fst tw + 1, snd tw)"
proof -
  fix tw 
  assume "inv_nout tw \<and> inv_nout2 tw \<and>  (disjnt {STATE, CTR_NEQ_0, OUTREADY_REG} (event_of tw)) "
  hence "inv_nout tw" and *: "inv_nout2 tw" and **: "disjnt {STATE, CTR_NEQ_0, OUTREADY_REG} (event_of tw)"
    by auto
  hence 0: "wline_of tw STATE (fst tw - 1) = wline_of tw STATE (fst tw)" and 
        1: "value_of CTR_NEQ_0 at_time (fst tw - 1) on tw = curr_value_of CTR_NEQ_0 on tw" and 
        2: "value_of OUTREADY_REG at_time (fst tw - 1) on tw = curr_value_of OUTREADY_REG on tw"
    unfolding event_of_alt_def 
    by (smt diff_is_0_eq' disjnt_insert1 le_numeral_extra(1) mem_Collect_eq)+
  have "bval_of (value_of NEXT_OUTREADYREG at_time fst tw + 1 on tw) = bval_of (value_of NEXT_OUTREADYREG at_time fst tw on tw)"
    using * ** unfolding inv_nout2_def by auto
  also have "... = (case wline_of tw STATE (fst tw - 1) of    
                       V_PROC \<Rightarrow> \<not> bval_of (value_of CTR_NEQ_0 at_time fst tw - 1 on tw) |
                       V_POST \<Rightarrow> bval_of (value_of OUTREADY_REG at_time fst tw - 1 on tw) |
                       _      \<Rightarrow>   False)"
    using `inv_nout tw` unfolding inv_nout_def by auto
  also have "... = (case wline_of tw STATE (fst tw) of    
                       V_PROC \<Rightarrow> \<not> bval_of (value_of CTR_NEQ_0 at_time fst tw  on tw) |
                       V_POST \<Rightarrow>   bval_of (value_of OUTREADY_REG at_time fst tw  on tw) |
                       _      \<Rightarrow>   False)"
    using `disjnt {STATE, CTR_NEQ_0, OUTREADY_REG} (event_of tw)` unfolding 0 1 2
    by auto
  finally show "inv_nout (fst tw + 1, snd tw)"
    unfolding inv_nout_def comp_def snd_conv fst_conv 
    by (auto split: val.splits signedness.splits list.splits bool.splits)
qed

lemma inv_nout_vproc_true:
  fixes tw
  assumes " curr_value_of STATE on tw = V_PROC"
  assumes " curr_value_of CTR_NEQ_0 on tw = Bv True"
  defines "tw' \<equiv> tw[ NEXT_OUTREADYREG, 1 :=\<^sub>2 Bv False]"
  assumes "wityping \<Gamma> (snd tw)"
  shows   "inv_nout (fst tw' + 1, snd tw')"
proof -
  have "bval_of (value_of NEXT_OUTREADYREG at_time fst tw' + 1 on (fst tw' + 1 , snd tw')) = 
        bval_of (value_of NEXT_OUTREADYREG at_time fst tw + 1 on tw')"
    unfolding tw'_def worldline_upd2_def worldline_upd_def by auto
  also have "... = False"
    unfolding tw'_def worldline_upd2_def worldline_upd_def by auto
  also have "... = (case wline_of tw STATE (fst tw) of    
                       V_PROC \<Rightarrow> \<not> bval_of (value_of CTR_NEQ_0 at_time fst tw  on tw) |
                       V_POST \<Rightarrow> bval_of (value_of OUTREADY_REG at_time fst tw on tw) |
                       _      \<Rightarrow>   False)"
    using assms(1-2) by (auto)
  finally show ?thesis
    unfolding inv_nout_def comp_def snd_conv fst_conv tw'_def worldline_upd2_def worldline_upd_def
    by (simp_all split: val.splits signedness.splits list.splits bool.splits)
qed

lemma inv_nout_vproc_false:
  fixes tw
  assumes " curr_value_of STATE on tw = V_PROC"
  assumes " curr_value_of CTR_NEQ_0 on tw \<noteq> Bv True"
  defines "tw' \<equiv> tw[ NEXT_OUTREADYREG, 1 :=\<^sub>2 Bv True]"
  assumes "wityping \<Gamma> (snd tw)"
  shows   "inv_nout (fst tw' + 1, snd tw')"
proof -
  have "type_of (snd (snd tw) CTR_NEQ_0 (get_time tw)) = Bty"
    using assms(4) cosine_locale_axioms unfolding cosine_locale_def wityping_def wtyping_def
    by auto
  hence *: "snd (snd tw) CTR_NEQ_0 (fst tw) = Bv False"
    using assms(2) by (smt comp_apply ty.distinct(1) type_of.elims)
  have "bval_of (value_of NEXT_OUTREADYREG at_time fst tw' + 1 on (fst tw' + 1 , snd tw')) = 
        bval_of (value_of NEXT_OUTREADYREG at_time fst tw + 1 on tw')"
    unfolding tw'_def worldline_upd2_def worldline_upd_def by auto
  also have "... = True"
    unfolding tw'_def worldline_upd2_def worldline_upd_def by auto
  also have "... = (case wline_of tw STATE (fst tw) of    
                       V_PROC \<Rightarrow> \<not> bval_of (value_of CTR_NEQ_0 at_time fst tw  on tw) |
                       V_POST \<Rightarrow> bval_of (value_of OUTREADY_REG at_time fst tw on tw) |
                       _      \<Rightarrow>   False)"
    using assms(1-2) * by (auto)
  finally show ?thesis
    unfolding inv_nout_def comp_def snd_conv fst_conv tw'_def worldline_upd2_def worldline_upd_def
    by (simp_all split: val.splits signedness.splits list.splits bool.splits)
qed

lemma inv_nout_vpost:
  fixes tw
  assumes " curr_value_of STATE on tw = V_POST"
  defines "tw' \<equiv> tw[ NEXT_OUTREADYREG, 1 :=\<^sub>2 eval_world_raw2 tw (Bsig OUTREADY_REG)]"
  assumes "wityping \<Gamma> (snd tw)"
  shows   "inv_nout (fst tw' + 1, snd tw')"
proof -
  have "bval_of (value_of NEXT_OUTREADYREG at_time fst tw' + 1 on (fst tw' + 1 , snd tw')) = 
        bval_of (value_of NEXT_OUTREADYREG at_time fst tw + 1 on tw')"
    unfolding tw'_def worldline_upd2_def worldline_upd_def by auto
  also have "... = bval_of (snd (snd tw) OUTREADY_REG (fst tw))"
    unfolding tw'_def worldline_upd2_def worldline_upd_def by auto
  also have "... = (case wline_of tw STATE (fst tw) of    
                       V_PROC \<Rightarrow> \<not> bval_of (value_of CTR_NEQ_0 at_time fst tw  on tw) |
                       V_POST \<Rightarrow> bval_of (value_of OUTREADY_REG at_time fst tw on tw) |
                       _      \<Rightarrow>   False)"
    using assms(1) by auto
  finally show ?thesis
    unfolding inv_nout_def comp_def snd_conv fst_conv tw'_def worldline_upd2_def worldline_upd_def
    by (simp_all split: val.splits signedness.splits list.splits bool.splits)
qed

lemma inv_nout_others:
  fixes tw
  assumes " curr_value_of STATE on tw \<noteq> V_PROC"
  assumes " curr_value_of STATE on tw \<noteq> V_POST"
  defines "tw' \<equiv> tw[ NEXT_OUTREADYREG, 1 :=\<^sub>2 Bv False]"
  assumes "wityping \<Gamma> (snd tw)"
  shows   "inv_nout (fst tw' + 1, snd tw')"
proof -
  have "bval_of (value_of NEXT_OUTREADYREG at_time fst tw' + 1 on (fst tw' + 1 , snd tw')) = 
        bval_of (value_of NEXT_OUTREADYREG at_time fst tw + 1 on tw')"
    unfolding tw'_def worldline_upd2_def worldline_upd_def by auto
  also have "... = False"
    unfolding tw'_def worldline_upd2_def worldline_upd_def by auto
  also have "... = (case wline_of tw STATE (fst tw) of    
                       V_PROC \<Rightarrow> \<not> bval_of (value_of CTR_NEQ_0 at_time fst tw  on tw) |
                       V_POST \<Rightarrow> bval_of (value_of OUTREADY_REG at_time fst tw on tw) |
                       _      \<Rightarrow>   False)"
    using assms(1-2) by (simp_all split:val.splits signedness.splits list.splits bool.splits)
  finally show ?thesis
    unfolding inv_nout_def comp_def snd_conv fst_conv tw'_def worldline_upd2_def worldline_upd_def
    by (simp_all split: val.splits signedness.splits list.splits bool.splits)  
qed

lemma inv_nout2: 
  fixes tw v
  defines "tw' \<equiv> tw[NEXT_OUTREADYREG, 1 :=\<^sub>2 v]"
  shows   "inv_nout2 (fst tw' + 1, snd tw')"
  unfolding inv_nout2_def tw'_def worldline_upd2_def worldline_upd_def by auto

lemma correctness_nout:                          
  "\<Gamma> \<turnstile>\<^sub>s \<lbrace>\<lambda>tw. inv_nout tw \<and> inv_nout2 tw\<rbrace> next_outready_reg \<lbrace>\<lambda>tw. inv_nout tw \<and> inv_nout2 tw\<rbrace>"
  apply (rule While_Suc)
  apply (rule Conseq'[where P="wp3_conc \<Gamma> next_outready_reg (\<lambda>tw. inv_nout  (fst tw + 1, snd tw) \<and> 
                                                                  inv_nout2 (fst tw + 1, snd tw))", rotated])  
  apply (rule wp3_conc_is_pre, rule conc_stmt_wf_next_outready_reg, rule nonneg_delay_conc_next_outready_reg, rule cwt_no, simp)
  unfolding next_outready_reg_def wp3_conc_single'[OF cwt_no[unfolded next_outready_reg_def] nonneg_delay_conc_next_outready_reg[unfolded next_outready_reg_def]] wp3_fun.simps
  apply (rule, rule, unfold if_bool_eq_conj, rule, rule, rule_tac[2] impI) 
  apply (rule_tac[2] impI | rule_tac[2] conjI)+  apply (rule_tac[4] impI | rule_tac[4] conjI)+
  apply (rule_tac[6] impI | rule_tac[6] conjI)+  apply (rule_tac[8] impI | rule_tac[8] conjI)+
  subgoal using inv_nout_preserved inv_nout2_preserved by auto subgoal by auto
  subgoal using inv_nout2 inv_nout_vproc_true by auto subgoal by auto
  subgoal using inv_nout2 inv_nout_vproc_false by auto subgoal by auto
  subgoal using inv_nout2 inv_nout_vpost by auto subgoal by auto
  subgoal using inv_nout2 inv_nout_others by auto
  done

lemma init_ensures_nout:
  "init_sim2_hoare_wt \<Gamma> (\<lambda>tw. fst tw = 0) next_outready_reg (\<lambda>tw. inv_nout tw \<and> inv_nout2 tw)"
  unfolding next_outready_reg_def
  apply (rule AssignI_suc, rule SingleI)
  apply (rule Conseq3[where Q="\<lambda>tw. inv_nout (fst tw + 1, snd tw) \<and> inv_nout2 (fst tw + 1, snd tw)", rotated])
  apply (rule wp3_fun_is_pre[OF seq_wt_next_outready_reg[unfolded next_outready_reg_def conc_stmt.sel(4)] nonneg_delay_next_outready_reg[unfolded next_outready_reg_def conc_stmt.sel(4)]], simp)
  apply (rule, rule, unfold wp3_fun.simps(4), unfold if_bool_eq_conj)
  apply (rule conjI | rule impI)+
   apply (rule_tac[2] impI | rule_tac[2] conjI)+  apply (rule_tac[3] impI | rule_tac[3] conjI)+
  subgoal unfolding wp3_fun.simps eval_world_raw.simps using inv_nout2 inv_nout_vproc_true inv_nout_vproc_false 
    by (metis comp_apply eval_world_raw.simps(10))
  subgoal unfolding wp3_fun.simps eval_world_raw.simps using inv_nout2 inv_nout_vpost
    by (metis comp_apply eval_world_raw.simps(10))
  subgoal unfolding wp3_fun.simps eval_world_raw.simps using inv_nout2 inv_nout_others
    by (metis comp_apply eval_world_raw.simps(10))
  done

lemma 
  assumes "sim_fin2 w (i + 1) next_outready_reg tw'" and "wityping \<Gamma> w"
  shows "inv_nout tw'"
  using grand_correctness[OF assms conc_stmt_wf_next_outready_reg cwt_no nonneg_delay_conc_next_outready_reg correctness_nout init_ensures_nout]
  by auto  

section \<open>Functional specification for @{term "ctr_neq_0"}\<close>

definition inv_n0 :: "sig assn2" where
  "inv_n0 tw = (bval_of (curr_value_of CTR_NEQ_0 on tw) \<longleftrightarrow> 0 < ubin_of COUNTER at_time fst tw - 1 on tw)"

definition inv_n02 :: "sig assn2" where
  "inv_n02 tw \<equiv> disjnt {COUNTER} (event_of tw) \<longrightarrow> 
          (\<forall>i > fst tw. bval_of (value_of CTR_NEQ_0 at_time i on tw) = bval_of (value_of CTR_NEQ_0 at_time fst tw on tw))"

lemma inv_n02_preserved:
  "\<And>tw. inv_n02 tw \<and> (disjnt {COUNTER} (event_of tw)) \<Longrightarrow> inv_n02 (fst tw + 1, snd tw)"
  unfolding inv_n02_def by auto

lemma inv_n0_preserved:
  "\<And>tw. inv_n0 tw \<and> inv_n02 tw \<and>  (disjnt {COUNTER} (event_of tw)) \<Longrightarrow> inv_n0 (fst tw + 1, snd tw)"
proof -
  fix tw 
  assume "inv_n0 tw \<and> inv_n02 tw \<and>  (disjnt  {COUNTER} (event_of tw)) "
  hence "inv_n0 tw" and *: "inv_n02 tw" and **: "disjnt  {COUNTER} (event_of tw)"
    by auto
  hence 0: "wline_of tw COUNTER (fst tw - 1) = wline_of tw COUNTER (fst tw)" 
    unfolding event_of_alt_def 
    by (smt diff_is_0_eq' disjnt_insert1 le_numeral_extra(1) mem_Collect_eq)+
  have "bval_of (value_of CTR_NEQ_0 at_time fst tw + 1 on tw) = bval_of (curr_value_of CTR_NEQ_0 on tw)"
    using ** * unfolding inv_n02_def by auto
  also have "...  \<longleftrightarrow> (0 < ubin_of COUNTER at_time fst tw - 1 on tw)"
    using `inv_n0 tw` unfolding inv_n0_def by auto
  also have "... \<longleftrightarrow> (0 < ubin_of COUNTER at_time fst tw on tw)"
    using 0 by auto
  finally show "inv_n0 (fst tw + 1, snd tw)"
    unfolding inv_n0_def by auto
qed

lemma inv_n0:
  fixes tw
  defines "tw' \<equiv> tw[ CTR_NEQ_0, 1 :=\<^sub>2 eval_world_raw2 tw (Bor (Bindex COUNTER 2) (Bor (Bindex COUNTER 1) (Bindex COUNTER 0)))]"
  assumes "wityping \<Gamma> (snd tw)"
  shows   "inv_n0 (fst tw' + 1, snd tw')"
proof -
  have *: "type_of (snd (snd tw) COUNTER (get_time tw)) = Lty Uns 3"
    using assms(2) cosine_locale_axioms unfolding wityping_def wtyping_def cosine_locale_def
    by auto
  hence len: "length (lval_of (wline_of tw COUNTER (get_time tw))) = 3"
    by (metis comp_def ty.inject ty.simps(3) type_of.elims val.sel(3))
  have "bval_of (value_of CTR_NEQ_0 at_time fst tw' + 1 on (fst tw' + 1, snd tw')) = 
        bval_of (value_of CTR_NEQ_0 at_time fst tw + 1 on tw')"
    unfolding tw'_def worldline_upd2_def worldline_upd_def by auto
  also have "... = (lval_of (curr_value_of COUNTER on tw) ! 2 \<or> lval_of (curr_value_of COUNTER on tw) ! 1 \<or> lval_of (curr_value_of COUNTER on tw) ! 0)"
    using * unfolding tw'_def worldline_upd2_def worldline_upd_def
    by (auto split: val.splits)
  also have "... \<longleftrightarrow> (0 < ubin_of COUNTER at_time fst tw on tw)"
  proof 
    assume asm: "lval_of (wline_of tw COUNTER (get_time tw)) ! 2 \<or> lval_of (wline_of tw COUNTER (get_time tw)) ! 1 \<or> lval_of (wline_of tw COUNTER (get_time tw)) ! 0"
    show "0 < ubin_of COUNTER at_time fst tw on tw "
    proof (rule ccontr)
      assume "\<not> 0 < ubin_of COUNTER at_time fst tw on tw"
      hence "ubin_of COUNTER at_time fst tw on tw \<le> 0"
        by auto
      hence "ubin_of COUNTER at_time fst tw on tw = 0"
        using bl_to_bin_ge0 by smt
      hence "bin_to_bl 3 (ubin_of COUNTER at_time fst tw on tw) = bin_to_bl 3 0"
        by auto
      also have "... = [False, False, False]"
        by auto
      finally have "bin_to_bl 3 (ubin_of COUNTER at_time fst tw on tw) = [False, False, False]"
        by auto
      hence "lval_of (wline_of tw COUNTER (get_time tw)) = [False, False, False]"
        using bl_bin_bl[of "lval_of (wline_of tw COUNTER (fst tw))"] len by auto 
      with asm show False 
        by auto
    qed
  next
    assume "0 < bl_to_bin (lval_of (wline_of tw COUNTER (get_time tw)))"
    thus   "lval_of (wline_of tw COUNTER (get_time tw)) ! 2 \<or> lval_of (wline_of tw COUNTER (get_time tw)) ! 1 \<or> lval_of (wline_of tw COUNTER (get_time tw)) ! 0"
    proof (rule contrapos_pp)
      have cases: "\<And> i ::nat. i < 3 \<Longrightarrow> i = 0 \<or> i = 1 \<or> i = 2"
        by auto
      assume "\<not> (lval_of (wline_of tw COUNTER (get_time tw)) ! 2 \<or> lval_of (wline_of tw COUNTER (get_time tw)) ! 1 \<or> lval_of (wline_of tw COUNTER (get_time tw)) ! 0)"
      hence " (\<not> lval_of (wline_of tw COUNTER (get_time tw)) ! 2 \<and> \<not> lval_of (wline_of tw COUNTER (get_time tw)) ! 1 \<and> \<not> lval_of (wline_of tw COUNTER (get_time tw)) ! 0)"
        by auto
      hence 2: "lval_of (curr_value_of COUNTER on tw) ! 2 = False" and 
            1: "lval_of (curr_value_of COUNTER on tw) ! 1 = False" and
            0: "lval_of (curr_value_of COUNTER on tw) ! 0 = False"
        by auto
      have "(\<forall>i<3. lval_of (wline_of tw COUNTER (get_time tw)) ! i = U_ZERO3 ! i)"
      proof (rule, rule)
        fix i  :: nat
        assume "i < 3"
        then consider "i = 0" | "i = 1" | "i = 2"
          by linarith
        thus "lval_of (wline_of tw COUNTER (get_time tw)) ! i = U_ZERO3 ! i "
          using 0 1 2 by cases auto
      qed
      hence "lval_of (curr_value_of COUNTER on tw) = [False, False, False]"
        using len unfolding list_eq_iff_nth_eq by auto
      hence "bl_to_bin (lval_of (wline_of tw COUNTER (get_time tw))) = 0"
        by auto
      thus "\<not> 0 < bl_to_bin (lval_of (wline_of tw COUNTER (get_time tw)))"
        by auto
    qed
  qed
  finally show ?thesis
    unfolding inv_n0_def fst_conv  comp_def snd_conv tw'_def worldline_upd2_def worldline_upd_def
    by auto
qed

lemma inv_n02: 
  fixes tw v
  defines "tw' \<equiv> tw[CTR_NEQ_0, 1 :=\<^sub>2 v]"
  shows   "inv_n02 (fst tw' + 1, snd tw')"
  unfolding inv_n02_def tw'_def worldline_upd2_def worldline_upd_def by auto

lemma correctness_n0:                          
  "\<Gamma> \<turnstile>\<^sub>s \<lbrace>\<lambda>tw. inv_n0 tw \<and> inv_n02 tw\<rbrace> ctr_neq_0 \<lbrace>\<lambda>tw. inv_n0 tw \<and> inv_n02 tw\<rbrace>"
  apply (rule While_Suc)
  apply (rule Conseq'[where P="wp3_conc \<Gamma> ctr_neq_0 (\<lambda>tw. inv_n0  (fst tw + 1, snd tw) \<and> 
                                                          inv_n02 (fst tw + 1, snd tw))", rotated]) 
  apply (rule wp3_conc_is_pre, rule conc_stmt_wf_ctr_neq_0, rule nonneg_delay_conc_ctr_neq_0, rule cwt_n0, simp)
  unfolding ctr_neq_0_def wp3_conc_single'[OF cwt_n0[unfolded ctr_neq_0_def] nonneg_delay_conc_ctr_neq_0[unfolded ctr_neq_0_def]] wp3_fun.simps
  apply (rule, rule, unfold if_bool_eq_conj, rule, rule, rule_tac[2] impI) 
  subgoal using inv_n0_preserved inv_n02_preserved by auto
  subgoal using inv_n02 inv_n0 by auto
  done

lemma init_ensures_n0:
  "init_sim2_hoare_wt \<Gamma> (\<lambda>tw. fst tw = 0) ctr_neq_0 (\<lambda>tw. inv_n0 tw \<and> inv_n02 tw)"
  unfolding ctr_neq_0_def
  apply (rule AssignI_suc, rule SingleI)
  apply (rule Conseq3[where Q="\<lambda>tw. inv_n0 (fst tw + 1, snd tw) \<and> inv_n02 (fst tw + 1, snd tw)", rotated])
  apply (rule wp3_fun_is_pre[OF seq_wt_ctr_neq_0[unfolded ctr_neq_0_def conc_stmt.sel(4)] nonneg_delay_ctr_neq_0[unfolded ctr_neq_0_def conc_stmt.sel(4)]], simp)
  apply (rule, rule, unfold wp3_fun.simps)
  using inv_n02 inv_n0 by blast

lemma 
  assumes "sim_fin2 w (i + 1) ctr_neq_0 tw'" and "wityping \<Gamma> w"
  shows "inv_n0 tw'"
  using grand_correctness[OF assms conc_stmt_wf_ctr_neq_0 cwt_n0 nonneg_delay_conc_ctr_neq_0 correctness_n0 init_ensures_n0]
  by auto  

section \<open>Functional specification for @{term "output"}\<close>

definition inv_output :: "sig assn2" where
  "inv_output tw = (curr_value_of OUTPUT on tw = value_of ACCUM at_time fst tw - 1 on tw)"

definition inv_output2 :: "sig assn2" where
  "inv_output2 tw \<equiv> disjnt {ACCUM} (event_of tw) \<longrightarrow> 
          (\<forall>i > fst tw. (value_of OUTPUT at_time i on tw) = (value_of OUTPUT at_time fst tw on tw))"

lemma inv_output2_preserved:
  "\<And>tw. inv_output2 tw \<and> (disjnt {ACCUM} (event_of tw)) \<Longrightarrow> inv_output2 (fst tw + 1, snd tw)"
  unfolding inv_output2_def by auto

lemma inv_output_preserved:
  "\<And>tw. inv_output tw \<and> inv_output2 tw \<and>  (disjnt {ACCUM} (event_of tw)) \<Longrightarrow> inv_output (fst tw + 1, snd tw)"
proof -
  fix tw 
  assume "inv_output tw \<and> inv_output2 tw \<and>  (disjnt  {ACCUM} (event_of tw)) "
  hence "inv_output tw" and *: "inv_output2 tw" and **: "disjnt  {ACCUM} (event_of tw)"
    by auto
  hence 0: "wline_of tw ACCUM (fst tw - 1) = wline_of tw ACCUM (fst tw)" 
    unfolding event_of_alt_def 
    by (smt diff_is_0_eq' disjnt_insert1 le_numeral_extra(1) mem_Collect_eq)+
  have " (value_of OUTPUT at_time fst tw + 1 on tw) = (curr_value_of OUTPUT on tw)"
    using ** * unfolding inv_output2_def by auto
  also have "... = value_of ACCUM at_time fst tw - 1 on tw"
    using `inv_output tw` unfolding inv_output_def by auto
  also have "... = value_of ACCUM at_time fst tw on tw"
    using 0 by auto
  finally show "inv_output (fst tw + 1, snd tw)"
    unfolding inv_output_def by auto
qed

lemma inv_output:
  fixes tw
  defines "tw' \<equiv> tw[ OUTPUT, 1 :=\<^sub>2 eval_world_raw2 tw (Bsig ACCUM)]"
  assumes "wityping \<Gamma> (snd tw)"
  shows   "inv_output (fst tw' + 1, snd tw')"
proof -          
  have "value_of OUTPUT at_time fst tw' + 1 on (fst tw' + 1, snd tw') = 
        value_of OUTPUT at_time fst tw + 1 on tw'"
    unfolding tw'_def worldline_upd2_def worldline_upd_def by auto
  also have "... = curr_value_of ACCUM on tw"
    unfolding tw'_def worldline_upd2_def worldline_upd_def by auto
  finally show ?thesis
    unfolding inv_output_def comp_def snd_conv fst_conv tw'_def worldline_upd2_def worldline_upd_def
    by auto
qed

lemma inv_output2: 
  fixes tw v
  defines "tw' \<equiv> tw[OUTPUT, 1 :=\<^sub>2 v]"
  shows   "inv_output2 (fst tw' + 1, snd tw')"
  unfolding inv_output2_def tw'_def worldline_upd2_def worldline_upd_def by auto

lemma correctness_output:                          
  "\<Gamma> \<turnstile>\<^sub>s \<lbrace>\<lambda>tw. inv_output tw \<and> inv_output2 tw\<rbrace> output \<lbrace>\<lambda>tw. inv_output tw \<and> inv_output2 tw\<rbrace>"
  apply (rule While_Suc)
  apply (rule Conseq'[where P="wp3_conc \<Gamma> output (\<lambda>tw. inv_output  (fst tw + 1, snd tw) \<and> 
                                                          inv_output2 (fst tw + 1, snd tw))", rotated]) 
  apply (rule wp3_conc_is_pre, rule conc_stmt_wf_output, rule nonneg_delay_conc_output, rule cwt_output, simp)
  unfolding output_def wp3_conc_single'[OF cwt_output[unfolded output_def] nonneg_delay_conc_output[unfolded output_def]] wp3_fun.simps
  apply (rule, rule, unfold if_bool_eq_conj, rule, rule, rule_tac[2] impI) 
  subgoal using inv_output_preserved inv_output2_preserved by auto
  subgoal using inv_output inv_output2 by auto
  done

lemma init_ensures_output:
  "init_sim2_hoare_wt \<Gamma> (\<lambda>tw. fst tw = 0) output (\<lambda>tw. inv_output tw \<and> inv_output2 tw)"
  unfolding output_def
  apply (rule AssignI_suc, rule SingleI)
  apply (rule Conseq3[where Q="\<lambda>tw. inv_output (fst tw + 1, snd tw) \<and> inv_output2 (fst tw + 1, snd tw)", rotated])
  apply (rule wp3_fun_is_pre[OF seq_wt_output[unfolded output_def conc_stmt.sel(4)] nonneg_delay_output[unfolded output_def conc_stmt.sel(4)]], simp)
  apply (rule, rule, unfold wp3_fun.simps)
  using inv_output inv_output2 by blast

lemma 
  assumes "sim_fin2 w (i + 1) output tw'" and "wityping \<Gamma> w"
  shows "inv_output tw'"
  using grand_correctness[OF assms conc_stmt_wf_output cwt_output nonneg_delay_conc_output correctness_output init_ensures_output]
  by auto  

section \<open>Functional specification for @{term "output_ready"}\<close>

definition inv_output_ready :: "sig assn2" where
  "inv_output_ready tw = (curr_value_of OUTREADY on tw = value_of OUTREADY_REG at_time fst tw - 1 on tw)"

definition inv_output2_ready :: "sig assn2" where
  "inv_output2_ready tw \<equiv> disjnt {OUTREADY_REG} (event_of tw) \<longrightarrow> 
          (\<forall>i > fst tw. (value_of OUTREADY at_time i on tw) = (value_of OUTREADY at_time fst tw on tw))"

lemma inv_output2_preserved_ready:
  "\<And>tw. inv_output2_ready tw \<and> (disjnt {OUTREADY_REG} (event_of tw)) \<Longrightarrow> inv_output2_ready (fst tw + 1, snd tw)"
  unfolding inv_output2_ready_def by auto

lemma inv_output_preserved_ready:
  "\<And>tw. inv_output_ready tw \<and> inv_output2_ready tw \<and>  (disjnt {OUTREADY_REG} (event_of tw)) \<Longrightarrow> inv_output_ready (fst tw + 1, snd tw)"
proof -
  fix tw 
  assume "inv_output_ready tw \<and> inv_output2_ready tw \<and>  (disjnt  {OUTREADY_REG} (event_of tw)) "
  hence "inv_output_ready tw" and *: "inv_output2_ready tw" and **: "disjnt  {OUTREADY_REG} (event_of tw)"
    by auto
  hence 0: "wline_of tw OUTREADY_REG (fst tw - 1) = wline_of tw OUTREADY_REG (fst tw)" 
    unfolding event_of_alt_def 
    by (smt diff_is_0_eq' disjnt_insert1 le_numeral_extra(1) mem_Collect_eq)+
  have " (value_of OUTREADY at_time fst tw + 1 on tw) = (curr_value_of OUTREADY on tw)"
    using ** * unfolding inv_output2_ready_def by auto
  also have "... = value_of OUTREADY_REG at_time fst tw - 1 on tw"
    using `inv_output_ready tw` unfolding inv_output_ready_def by auto
  also have "... = value_of OUTREADY_REG at_time fst tw on tw"
    using 0 by auto
  finally show "inv_output_ready (fst tw + 1, snd tw)"
    unfolding inv_output_ready_def by auto
qed

lemma inv_output_ready:
  fixes tw
  defines "tw' \<equiv> tw[ OUTREADY, 1 :=\<^sub>2 eval_world_raw2 tw (Bsig OUTREADY_REG)]"
  assumes "wityping \<Gamma> (snd tw)"
  shows   "inv_output_ready (fst tw' + 1, snd tw')"
proof -          
  have "value_of OUTREADY at_time fst tw' + 1 on (fst tw' + 1, snd tw') = 
        value_of OUTREADY at_time fst tw + 1 on tw'"
    unfolding tw'_def worldline_upd2_def worldline_upd_def by auto
  also have "... = curr_value_of OUTREADY_REG on tw"
    unfolding tw'_def worldline_upd2_def worldline_upd_def by auto
  finally show ?thesis
    unfolding inv_output_ready_def comp_def snd_conv fst_conv tw'_def worldline_upd2_def worldline_upd_def
    by auto
qed

lemma inv_output2_ready: 
  fixes tw v
  defines "tw' \<equiv> tw[OUTREADY, 1 :=\<^sub>2 v]"
  shows   "inv_output2_ready (fst tw' + 1, snd tw')"
  unfolding inv_output2_ready_def tw'_def worldline_upd2_def worldline_upd_def by auto

lemma correctness_output_ready:                          
  "\<Gamma> \<turnstile>\<^sub>s \<lbrace>\<lambda>tw. inv_output_ready tw \<and> inv_output2_ready tw\<rbrace> output_ready \<lbrace>\<lambda>tw. inv_output_ready tw \<and> inv_output2_ready tw\<rbrace>"
  apply (rule While_Suc)
  apply (rule Conseq'[where P="wp3_conc \<Gamma> output_ready (\<lambda>tw. inv_output_ready  (fst tw + 1, snd tw) \<and> 
                                                          inv_output2_ready (fst tw + 1, snd tw))", rotated]) 
  apply (rule wp3_conc_is_pre, rule conc_stmt_wf_output_ready, rule nonneg_delay_conc_output_ready, rule cwt_outready, simp)
  unfolding output_ready_def wp3_conc_single'[OF cwt_outready[unfolded output_ready_def] nonneg_delay_conc_output_ready[unfolded output_ready_def]] wp3_fun.simps
  apply (rule, rule, unfold if_bool_eq_conj, rule, rule, rule_tac[2] impI) 
  subgoal using inv_output_preserved_ready inv_output2_preserved_ready by auto
  subgoal using inv_output_ready inv_output2_ready by auto
  done

lemma init_ensures_output_ready:
  "init_sim2_hoare_wt \<Gamma> (\<lambda>tw. fst tw = 0) output_ready (\<lambda>tw. inv_output_ready tw \<and> inv_output2_ready tw)"
  unfolding output_ready_def
  apply (rule AssignI_suc, rule SingleI)
  apply (rule Conseq3[where Q="\<lambda>tw. inv_output_ready (fst tw + 1, snd tw) \<and> inv_output2_ready (fst tw + 1, snd tw)", rotated])
  apply (rule wp3_fun_is_pre[OF seq_wt_output_ready[unfolded output_ready_def conc_stmt.sel(4)] nonneg_delay_output_ready[unfolded output_ready_def conc_stmt.sel(4)]], simp)
  apply (rule, rule, unfold wp3_fun.simps)
  using inv_output_ready inv_output2_ready by blast

lemma 
  assumes "sim_fin2 w (i + 1) output_ready tw'" and "wityping \<Gamma> w"
  shows "inv_output_ready tw'"
  using grand_correctness[OF assms conc_stmt_wf_output_ready cwt_outready nonneg_delay_conc_output_ready correctness_output_ready init_ensures_output_ready]
  by auto  

end

end
 