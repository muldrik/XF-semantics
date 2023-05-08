Require Import Events.
Require Import Execution.
Require Import Labels.
Require Import TSOFPGA.
Require Import Lia.
Require Import Arith.
Require Import IndefiniteDescription.
Require Import PropExtensionality.
Require Import List.
Require Import AuxProp.
Require Import AuxRel.
Import ListNotations.
From hahn Require Import Hahn.

Section CounterExample.

(* Definition winit := InitEvent(0). *)
(* Definition w1 := FpgaEvent (Fpga_write_req 1 0 1) 0 0.
Definition f1 := FpgaEvent (Fpga_fence_req_one 1) 1 1.
Definition f2 := FpgaEvent (Fpga_fence_req_one 2) 2 2.
Definition w2 := FpgaEvent (Fpga_write_req 2 0 2) 3 3.
Definition fall := FpgaEvent (Fpga_fence_req_all) 4 4.
Definition r0 := FpgaEvent (Fpga_read_req 2 0) 5 5.
Definition f2_resp := FpgaEvent (Fpga_fence_resp_one 2) 6 2.
Definition w2_resp := FpgaEvent (Fpga_write_resp 2 0 2) 7 3.
Definition w1_resp := FpgaEvent (Fpga_write_resp 1 0 1) 8 0.
Definition f1_resp := FpgaEvent (Fpga_fence_resp_one 1) 9 1.
Definition fall_resp := FpgaEvent (Fpga_fence_resp_all) 10 4.
Definition r0_resp := FpgaEvent (Fpga_read_resp 2 0 1) 11 5.

(* Простейший контрпример:
   w1
   f1
   f2
   w2
   f2_resp
   w2_resp
   w1_resp
   f1_resp
*)

(*
  w1
  f1
  f2
  w2
  fall_req
  ... случаются кеки:
    f2_resp
    w2_resp (чел попал в канал).
    w1_resp
    f2_resp.
  fall_resp
  r0_req
  r0_resp.

  В операционной семантике r0_resp не мог прочитать w1_resp, так как к моменту
  f2 в памяти уже лежат w1.
*)

(* В операционной семантике невозможна последовательность *)
(* w1 -> f1 -> f2 -> w2 -> f2_resp -> w1_resp -> f1_resp*)

(* В операционной семантике w2 не может оказаться в памяти раньше w1 *)

(* В результате неё в памяти окажется *)

(* В операционной возможно только следующее: *)
(* w1 в буфер -> f1 в буфер -> w2 в буфер -> f2 в буфер -> r0 в буфер.

 *)

Definition event_list := [w1; f1; f2; w2; fall; r0; w1_resp; f1_resp; f2_resp; w2_resp; fall_resp; r0_resp].
Definition EG := fun e => In e event_list \/ is_init e.

Definition exec_rf := fun e1 e2 => e1 = w2_resp /\ e2 = r0_resp.
Definition exec_co := fun e1 e2 => 
    ((is_init e1 /\ e2 = w1_resp) \/
    (e1 = w2_resp /\ e2 = w1_resp) \/
    (is_init e1 /\ e2 = w2_resp)) /\ same_loc e1 e2.

Definition G :=
  {| acts := EG;
     co := exec_co;
     rf := exec_rf;
     readpair := ⦗EG ∩₁ is_rd_req⦘ ⨾ req_resp_pair ⨾ ⦗EG ∩₁ is_rd_resp⦘;
     writepair := ⦗EG ∩₁ is_wr_req⦘ ⨾ req_resp_pair ⨾ ⦗EG ∩₁ is_wr_resp⦘;
     fenceonepair := ⦗EG ∩₁ is_fence_req_one⦘ ⨾ req_resp_pair ⨾ ⦗EG ∩₁ is_fence_resp_one⦘;
     fenceallpair := ⦗EG ∩₁ is_fence_req_all⦘ ⨾ req_resp_pair ⨾ ⦗EG ∩₁ is_fence_resp_all⦘
     |}.

Ltac unfolder'' := unfolder; unfolder'; unfold EG, exec_rf, exec_co, is_init, same_loc in *; simpl in *.

Lemma WFG: Wf G.
Proof.
    split; ins; desf.
    all: try by (unfolder''; split; ins; desf; auto 20).
    all: try by (unfolder''; ins; desf; auto 20).
    unfolder''; unfold codom_rel; ins; desf.
    exists w2_resp.
    auto.
Qed.

Lemma WF_FPGA_G: Wf_fpga G.
Proof.
    split; ins; desf.
    all: try basic_solver.
    (* - red; split; red. ins. apply seq_eqv_lr in H. apply seq_eqv_lr; unfolder''; desf. intuition. eauto 10. *)
    - unfolder''. ins; desf. exists r0_resp; intuition; desf. unfold r0, r0_resp in *. desf.
    - unfolder''. ins; desf. 
        { exists w1_resp; intuition; desf; unfold w1, w1_resp in *; desf. }
        { exists w2_resp. intuition; desf; unfold w2, w2_resp in *; desf. } 
    - unfolder''. ins; desf.
        { exists f1_resp; intuition; desf; unfold f1, f1_resp in *; desf. }
        { exists f2_resp. intuition; desf; unfold f2, f2_resp in *; desf. }
    - unfolder''. ins; desf. exists fall_resp; intuition; desf. unfold fall, fall_resp in *. desf.
Qed.

Ltac unfolder''' := unfold poloc, fr, rf, co, sb, exec_rf, exec_co, same_loc, is_init, is_cpu, ext_sb in *.
Ltac unfold_nodes := unfold w1, w2, f1, f2, fall, r0, w1_resp, w2_resp, f1_resp, f2_resp, fall_resp, r0_resp in *.

Lemma rf_in_sb: rf G ⊆ sb G.
Proof.
    unfolder; ins; desf. unfolder'''. desf. apply seq_eqv_lr; splits; simpl in *; red; simpl; intuition.  
Qed.

(* Lemma co_in_sb: co G ⊆ sb G.
Proof.
    unfolder; ins; desf; unfolder'''; desf; apply seq_eqv_lr; splits; simpl in *; try red; simpl; intuition.
Qed. *)

(* Lemma fr_in_sb: fr G ⊆ fun e1 e2 => e1 = r0_resp /\ e2 = w1_resp.
Proof.
    red; ins; red in H.
    apply seq_eqv_lr.
    destruct H. destruct H. destruct H. destruct H.
    splits; simpl in *; unfold EG in *; simpl in *; unfolder'''; unfold_nodes; desf; intu
Qed.

Lemma fr_empty: fr G ⊆ ∅₂.
Proof.
    red; ins; red in H.
    destruct H. destruct H. destruct H. destruct H.
    simpl in H1; desf.
    unfold exec_co in *; destruct y; desf.
Qed. *)

Lemma ppoCpu_empty: ppoCpu G ⊆ ∅₂.
Proof.
    red; ins; red in H.
    destruct H.
    destruct H, H0.
    apply seq_eqv_lr in H.
    desf; simpl in *.
    unfold EG, is_cpu in *; simpl in *; desf.
Qed.


Lemma fence_structure: fence G ⊆ fun e1 e2 => e1 = w1_resp /\ e2 = fall_resp.
Proof.
    red; ins; red in H.
    destruct H.
    { red in H; destruct H. destruct H. destruct H0.
      destruct H0.
      red in H0; destruct H0; subst.
      apply seq_eqv_lr in H.
      simpl in *; destruct H; unfold EG, is_cpu_fence in *; simpl in *; desf. }
    red in H.
    repeat destruct H.
    destruct H0.
    destruct H.
    destruct H0.
    destruct H0.
    repeat destruct H2.
    (* unfold poFnRsp in *. *)
    apply seq_eqv_lr in H0.
    desf; simpl in *.
    red in H3; desf.
    destruct H.
    { destruct H as [x0' [POCH FN_ONE]].
      repeat destruct FN_ONE; subst.
      destruct POCH as [SB SCH].
      apply seq_eqv_lr in SB.
      destruct SB as [EGX [SB _]].
      simpl in *.
      unfold is_fence_resp_one in *.
      unfold ext_sb in *.
      unfold EG in H0; simpl in *; desf;
      unfold_nodes;
      unfold same_ch, chan_opt, fpga_chan_opt in *;
      unfold EG in EGX; simpl in *; desf; unfold_nodes; desf;
      unfold EG in H3; simpl in *; desf; unfold_nodes; desf; lia. }

    destruct H as [x0' [SB FN_ALL]].
    repeat destruct FN_ALL; subst.
    apply seq_eqv_lr in SB.
    destruct SB as [EGX [SB _]].
    simpl in *.
    unfold is_fence_resp_all in *.
    unfold ext_sb in *.
    unfold EG in H0; simpl in *; desf;
    unfold_nodes;
    unfold same_ch, chan_opt, fpga_chan_opt in *;
    unfold EG in EGX; simpl in *; desf; unfold_nodes; desf;
    unfold EG in H3; simpl in *; desf; unfold_nodes; desf; lia.
Qed. 

Lemma fr_structure: fr G ≡ fun e1 e2 => e1 = r0_resp /\ e2 = w1_resp.
Proof.
  red; ins; split.
  { red; ins. red in H.
    do 3 (destruct H).
    simpl in H.
    red in H.
    destruct H; subst.
    destruct H1.
    desf.
   }
  red; ins.
  red; red; splits; red; ins.
  2: { cbv in *; desf. }
  exists w2_resp.
  unfold exec_rf, exec_co, EG in *.
  simpl in *. desf; intuition.
  unfold same_loc; desf.
Qed.

Lemma ppoFpga_lemma: ppoFpga G ⊆ ⦗fun e => e <> r0_resp⦘ ⨾ (ppoFpga G) ⨾ ⦗fun e => e <> r0_resp⦘ ∪ (fun e1 e2 => e1 = r0 /\ e2 = r0_resp).
Proof.
  red; ins; desf.
  remember H as H'.
  clear HeqH'.
  red in H.
  destruct H as [[POCH | SB] | PAIR].
  { apply seq_eqv_lr in POCH.
    left; apply seq_eqv_lr.
    destruct POCH as [RSP [[SB SCH] NOTR]].
    apply seq_eqv_lr in SB.
    simpl in *; desf.
    unfold ext_sb, is_resp, minus_event, is_rd_resp in *.
    splits; vauto;
    intro; subst;
    unfold EG in *; simpl in *; desf; unfold_nodes; desf; lia.
   }
  { apply seq_eqv_lr in SB.
    left; apply seq_eqv_lr.
    destruct SB as [RSP [SB NOTR]].
    apply seq_eqv_lr in SB.
    simpl in *; desf.
    unfold ext_sb, is_resp, minus_event, is_rd_resp in *.
    splits; vauto;
    intro; subst;
    unfold EG in *; simpl in *; desf; unfold_nodes; desf; lia.
   }
   red in PAIR.
   destruct PAIR as [[[RP | P] | P] | P].
   { right. simpl in *. apply seq_eqv_lr in RP.
     desf; unfold EG in *; unfolder'; simpl in *; desf. }
    all: 
    (left; simpl in *; apply seq_eqv_lr in P;
    desf; apply seq_eqv_lr; splits; vauto; intro; subst;
    unfold EG in *; unfolder'; simpl in *; desf).
Qed.

Lemma Consistent: Ax86Consistent G.
Proof.
    split.
    (* { simpl in *. unfold exec_rf, exec_co.
    arewrite (rf G ⊆ sb G) by apply rf_in_sb.
      arewrite (co G ⊆ sb G) by apply co_in_sb. *)
    
    {
        cut ((poloc G ∪ rf G ∪ co G ∪ fr G) ∩ is_cpu × is_cpu ⊆ ∅₂).
        { ins. rewrite H. red. rewrite tc_empty. basic_solver. }
        repeat (rewrite inter_union_l).
        red; ins; desf. destruct H. destruct H. destruct H.
        destruct H. red in H. 
        - destruct H, H0. unfolder'''. apply seq_eqv_lr in H. simpl in *. unfold EG in *. simpl in *; desf.
        - destruct H, H0. unfolder'''. simpl in *. unfold EG in *. simpl in *; desf.
        - destruct H, H0. unfolder'''. simpl in *. unfold EG in *. simpl in *; desf.
        - destruct H, H0. red in H. do 3 (destruct H). red in H. simpl in *. unfolder'''. simpl in *. unfold EG in *. simpl in *; desf. }
    {
        Print acyclic.
        unfold ppo.
        arewrite (ppoCpu G ⊆ ∅₂) by apply ppoCpu_empty.
        rewrite (union_false_l).
        do 3 (rewrite unionA).
        rewrite unionC.
        rewrite <- unionA.
        rewrite <- unionA.
        rewrite (ppoFpga_lemma).
        rewrite <- unionA.
        apply acyclic_union.
        2: { admit. (* Первое ребро заканчивается в r0_resp, вторые в нем не начинаются *) }
        rewrite unionA.
        rewrite unionC.
        rewrite <- unionA.
        rewrite <- unionA.
        apply acyclic_union.
        { admit. (* Вложено в SB *)}
        
        (* Первое ребро выходит из r_resp. Вторые ребра не заходят в r_resp *)

        (* if starts with a read_req, cannot go to read_req *)
        (* noting goes to read_req *)
        (* if starts with a read_resp, only read_req cannot *)
        (* r0 -> w2 *)
        (* EG \ (read_req) *)
        (* sb \ (read_resp)*)
        
        arewrite (fre G ⊆ fr G).
        rewrite fr_structure.
        rewrite fence_structure.
        arewrite (rfe G ⊆ rf G).
        simpl; unfold exec_rf, exec_co.
        admit.
       }
    all: try by (rewrite fr_empty; repeat (rewrite seq_false_l); basic_solver).
    { red; ins; desf.
      destruct H as [x0 [FR [x1 [POCH RP]]]].
      apply seq_eqv_lr in RP.
      desf.
      apply fr_structure in FR; desf; subst.
      destruct POCH as [SB [CH CH']].
      destruct RP, RP1.
      unfold EG, is_rd_req,is_rd_resp, req_resp_pair in *; simpl in *; desf. }
    { red; ins; desf.
      destruct H as [x0 [FR [x1 [POFN [x2 [SB PAIR]]]]]] .
      apply fr_structure in FR; desf; subst.
      apply seq_eqv_lr in PAIR.
      desf.
      destruct PAIR as [EG2 REQ2]; unfold EG in EG2; unfold is_rd_req in *; simpl in *; desf.
      rewrite <- Heq in *; clear Heq.
      apply seq_eqv_lr in SB; simpl in *; destruct SB as [EG1 [SB _]].
      destruct POFN as [FF | FF];
      apply seq_eqv_r in FF; desf; unfold is_fence_resp_one, is_fence_resp_all, ext_sb in *; unfold EG in EG1; simpl in *; desf.
      - unfold f1_resp in *; desf; lia. 
      - unfold f2_resp in *; desf; lia. 
      - unfold fall_resp in *; desf; lia. 
     }
    { simpl; red; ins; desf. red in H. desf. 
      apply seq_eqv_lr in H0; unfold exec_rf in *; desf. simpl in *; lia. }
    (* { arewrite (fre G ⊆ fr G). rewrite fr_empty; repeat (rewrite seq_false_l); basic_solver. } *)
    { arewrite (rfe G ⊆ rf G).
      arewrite (fre G ⊆ fr G).
      rewrite (fr_structure).
      simpl; unfold exec_rf.
      red; ins; cbv in *; desf. }
    2: { red; ins.
      destruct H as [x0 [POCH [x1 [FENCE [x2 [SB PAIR]]]]]].
      apply seq_eqv_lr in FENCE.
      apply seq_eqv_lr in PAIR.
      apply seq_eqv_lr in SB.
      destruct POCH as [SB' SCH].
      apply seq_eqv_lr in SB'.
      simpl in *.
      desf.
      destruct FENCE, FENCE1.
      unfold EG in H1, SB1.
      simpl in *.
      red in H0, FENCE0, H2.
      red in SB0.
      destruct PAIR, PAIR1.
      unfold w1, w1_resp, f1, f1_resp, w2, w2_resp, f2, f2_resp, fall, fall_resp, r0, r0_resp, is_init in *.
      destruct x0, x1; desf; try lia.
      { destruct FENCE0; subst.
        unfold EG in SB'0, SB'1.
        simpl in *.
        desf.
        unfold f2 in *.
        desf.
        unfold EG in SB'.
        simpl in *.
        unfold ext_sb, same_ch, chan_opt, fpga_chan_opt in *;  simpl in *;  desf.
        unfold w2 in *; desf; lia. }
      { destruct FENCE0; subst.
        unfold EG in SB'0, SB'1.
        simpl in *.
        desf.
        unfold f2 in *.
        desf.
        unfold EG in SB'.
        simpl in *.
        unfold ext_sb, same_ch, chan_opt, fpga_chan_opt in *;  simpl in *;  desf.
        unfold w2 in *; desf; lia. }}
    { red; ins.
      destruct H as [x0 [SB' [x1 [FENCE [x2 [SB PAIR]]]]]].
      apply seq_eqv_lr in FENCE.
      apply seq_eqv_lr in PAIR.
      apply seq_eqv_lr in SB.
      apply seq_eqv_lr in SB'.
      simpl in *.
      desf.
      destruct FENCE, FENCE1.
      unfold EG in H1, SB1.
      simpl in *.
      red in H0, FENCE0, H2.
      red in SB0.
      destruct PAIR, PAIR1.
      unfold w1, w1_resp, f1, f1_resp, w2, w2_resp, f2, f2_resp, fall, fall_resp, r0, r0_resp, is_init in *.
      destruct x0, x1; desf; try lia. }
    { red; ins.
      destruct H as [x0 [SB' [x1 [PAIR [x2 [SB FENCE]]]]]].
      apply seq_eqv_lr in FENCE.
      apply seq_eqv_lr in PAIR.
      apply seq_eqv_lr in SB.
      apply seq_eqv_lr in SB'.
      simpl in *.
      desf.
      destruct FENCE, FENCE1.
      unfold EG in H1, SB1.
      simpl in *.
      red in H0, FENCE0, H2.
      red in SB0.
      destruct PAIR, PAIR1.
      unfold w1, w1_resp, f1, f1_resp, w2, w2_resp, f2, f2_resp, fall, fall_resp, r0, r0_resp, is_init in *.
      destruct x0, x1; desf; try lia.
      unfold ext_sb in *.
      unfold EG in SB'; simpl in *; desf.
      unfold fall in *; desf.
      unfold EG in SB'1; simpl in *; desf.
      - unfold w1 in *; desf; lia.
      - unfold w2 in *; desf; lia. }
    { red; ins.
      destruct H as [x0 [POCH [x1 [PAIR [x2 [SB FENCE]]]]]].
      apply seq_eqv_lr in FENCE.
      apply seq_eqv_lr in PAIR.
      apply seq_eqv_lr in SB.
      destruct POCH as [SB' SCH].
      apply seq_eqv_lr in SB'.
      simpl in *.
      desf.
      destruct FENCE, FENCE1.
      unfold EG in H1, SB1.
      simpl in *.
      red in H0, FENCE0, H2.
      red in SB0.
      destruct PAIR, PAIR1.
      unfold w1, w1_resp, f1, f1_resp, w2, w2_resp, f2, f2_resp, fall, fall_resp, r0, r0_resp, is_init in *.
      destruct x0, x1; desf; try lia.
      { unfold ext_sb in *.
        unfold EG in SB'; simpl in *; desf.
        unfold fall in *; desf.
        unfold ext_sb, same_ch, chan_opt, fpga_chan_opt in *;  simpl in *;  desf.
        unfold EG in SB'1; simpl in *; desf.
        unfold w1 in *; desf; lia. }
      unfold ext_sb in *.
      unfold EG in SB'; simpl in *; desf.
      unfold fall in *; desf.
      unfold ext_sb, same_ch, chan_opt, fpga_chan_opt in *;  simpl in *;  desf.
      unfold EG in SB'1; simpl in *; desf.
      unfold w2, f2 in *; desf.
      unfold EG in H5; simpl in *; desf.
      unfold w2_resp in *; desf. lia. }
Qed. *)

End CounterExample.