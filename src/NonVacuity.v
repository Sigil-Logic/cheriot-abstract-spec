(*
 * Copyright 2026 Sigil Logic
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 *     https://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 *)

(** * Non-vacuity of the theorem's hypotheses

    [ThreadIsolatedMonotonicity] (Properties.v) is proved under three hypotheses: a
    well-formed configuration ([WFConfig]), a valid initial machine
    ([ValidInitialMachine]), and, carried by every general instruction the decoder
    delivers, the per-instruction well-formedness [WfGeneralInst].  None of the five
    proof files exhibits anything satisfying them.  This file does, so that the theorem is
    seen to say something about at least one machine:

    - [RegisterInstructions]: two concrete general instructions, a no-op and a register
      move, each with [WfGeneralInst] proved, so the instruction type [Inst] is inhabited
      by a general instruction;
    - [Untagged]: what [ReachableCap] reduces to in a memory without tags, from
      capabilities without keys, which is what the configuration's well-formedness rests on;
    - [WitnessConfiguration]: a one-compartment, one-thread configuration and its initial
      machine, with [WFConfig] and [ValidInitialMachine] proved; the theorem applied to
      them ([theoremInstance]); and one same-domain step the machine takes
      ([machine0_step]).

    Every result here is closed under the global context ([Print Assumptions]); the only
    parameter left open is the capability encoding, which nothing here exercises.  Nothing
    here is imported by the proof files, and nothing in them changes. *)

From Stdlib Require Import List Lia Bool Nat PeanoNat.
Set Primitive Projections.
From cheriot Require Import Utils Tactics Spec SpecLemmas Properties.

Import ListNotations.

(** ** Two list facts the register move needs *)
Section Lists.
  Lemma In_firstn : forall A n (l: list A) x, In x (firstn n l) -> In x l.
  Proof.
    induction n as [|n IH]; intros l x H; destruct l as [|a l]; cbn in H; try contradiction.
    destruct H as [H|H]; [left; exact H | right; apply (IH _ _ H)].
  Qed.

  Lemma In_skipn : forall A n (l: list A) x, In x (skipn n l) -> In x l.
  Proof.
    induction n as [|n IH]; intros l x H; destruct l as [|a l]; cbn in H; try contradiction.
    - exact H.
    - right; apply (IH _ _ H).
  Qed.
End Lists.

(** ** Register-only instructions

    An instruction that reads and writes the register file and the program counter, and
    never touches memory, satisfies [FuncNormal] and [FuncSystem] outright (its two runs
    on any two memories agree) and leaves every memory-update obligation reflexive.  The
    combinator [regInst] builds such an instruction from a function on the user thread
    state; [liftInst] lifts a normal instruction to a general one that leaves the system
    context alone.  [RegInstOk] is what remains to be shown of the function: it runs only
    with an executable PCC, reaches no new capability, keeps the PCC executable, and
    preserves the register count.  [regInst_WfGeneralInst] discharges [WfGeneralInst] from
    it, once, for every such instruction. *)
Section RegisterInstructions.
  Context [ISA: ISA_params].
  Context {machineTypeParams: MachineTypeParams}.
  Context {capEncodeDecode: CapEncodeDecode}.

  (** Register [rd] of [rf] set to [v]; the other registers unchanged. *)
  Definition setReg (rf: RegisterFile) (rd: nat) (v: CapOrBytes) : RegisterFile :=
    firstn rd rf ++ v :: skipn (S rd) rf.

  Lemma setReg_length : forall rf rd v, rd < length rf -> length (setReg rf rd v) = length rf.
  Proof.
    intros; unfold setReg. rewrite length_app, length_firstn.
    change (length (v :: skipn (S rd) rf)) with (S (length (skipn (S rd) rf))).
    rewrite length_skipn, PeanoNat.Nat.min_l by lia. lia.
  Qed.

  Lemma setReg_In : forall rf rd v x, In x (setReg rf rd v) -> x = v \/ In x rf.
  Proof.
    intros * H; unfold setReg in H. apply in_app_or in H. destruct H as [H|[H|H]].
    - right; eapply In_firstn; eauto.
    - subst; left; reflexivity.
    - right; eapply In_skipn; eauto.
  Qed.

  (** The PCC check every instruction below makes: unsealed, with execute permission. *)
  Definition execPCCb (pcc: Cap) : bool :=
    negb (isSealed pcc) && existsb (Perm.t_beq Perm.Exec) pcc.(capPerms).

  Lemma execPCCb_true : forall pcc,
      execPCCb pcc = true -> pcc.(capSealed) = None /\ In Perm.Exec pcc.(capPerms).
  Proof.
    intros pcc H. unfold execPCCb in H. apply andb_true_iff in H as [Hs He].
    split.
    - apply negb_true_iff in Hs. unfold isSealed in Hs.
      destruct (capSealed pcc); [discriminate | reflexivity].
    - apply existsb_exists in He as [p [Hp Hpe]].
      destruct p; cbn in Hpe; try discriminate; exact Hp.
  Qed.

  (** The PCC advanced by one four-byte instruction. *)
  Definition advancePCC (pcc: Cap) : Cap := updateCapCursor pcc (fun c => c + 4).

  (** Advancing an unsealed capability's cursor is a [Restrict] step: [RestrictUnsealed]
      constrains every field but the cursor. *)
  Lemma advancePCC_Restrict : forall pcc, pcc.(capSealed) = None -> Restrict pcc (advancePCC pcc).
  Proof.
    intros pcc Hs. unfold Restrict. rewrite Hs.
    constructor; cbv [SealEq advancePCC updateCapCursor setCapCursor]; cbn;
      first [reflexivity | apply Subset_refl].
  Qed.

  (** A normal instruction from a function on the user thread state: memory passes
      through. *)
  Definition regInst (f: UserThreadState -> Result ExnInfo UserThreadState)
             (uc: UserContext) : Result ExnInfo UserContext :=
    match f (fst uc) with
    | Ok uts' => Ok (uts', snd uc)
    | Exn e => Exn e
    end.

  (** A general instruction from a normal one: the system context passes through. *)
  Definition liftInst (ni: UserContext -> Result ExnInfo UserContext)
             (uc: UserContext) (sc: SystemContext)
    : Result ExnInfo (UserContext * SystemContext) :=
    match ni uc with
    | Ok uc' => Ok (uc', sc)
    | Exn e => Exn e
    end.

  (** What [regInst_WfGeneralInst] needs of the function: whenever it succeeds on a valid
      register file, the PCC it ran under was executable, the capabilities it produces were
      reachable from those it was given (in any memory, since it loads nothing), the new PCC
      is executable, and the register count is kept. *)
  Definition RegInstOk (f: UserThreadState -> Result ExnInfo UserThreadState) : Prop :=
    forall rf pcc, ValidRf rf ->
      match f (Build_UserThreadState rf pcc) with
      | Ok uts' =>
          In Perm.Exec pcc.(capPerms)
          /\ (forall mem, ReachableCaps mem (pcc :: capsOfRf rf)
                                       (uts'.(thread_pcc) :: capsOfRf uts'.(thread_rf)))
          /\ In Perm.Exec uts'.(thread_pcc).(capPerms)
          /\ ValidRf uts'.(thread_rf)
      | Exn _ => True
      end.

  (** An unchanged memory is a valid update of itself: every clause of [ValidMemUpdate]
      is conditioned on a difference. *)
  Lemma ValidMemUpdate_refl : forall mem caps, ValidMemUpdate mem caps mem.
  Proof.
    intros; split; [|split].
    - intros capa c Hne _; exfalso; apply Hne; reflexivity.
    - intros capa H1 H2; rewrite H1 in H2; discriminate.
    - intros a Hne; exfalso; apply Hne; reflexivity.
  Qed.

  (** Two unchanged memories satisfy [UpdatedMemSame], which only constrains addresses
      that changed. *)
  Lemma UpdatedMemSame_refl : forall m1 m2, UpdatedMemSame m1 m2 m1 m2.
  Proof.
    intros; split; intros a [H|H]; exfalso; apply H; reflexivity.
  Qed.

  Lemma regInst_FuncNormal : forall f, FuncNormal (regInst f).
  Proof.
    intros f. unfold FuncNormal. intros rf pcc m1 m2 _.
    unfold regInst; cbn.
    destruct (f (Build_UserThreadState rf pcc)) as [uts'|e].
    - split; [reflexivity | apply UpdatedMemSame_refl].
    - reflexivity.
  Qed.

  Lemma regInst_WfNormalInst : forall f, RegInstOk f -> WfNormalInst (regInst f).
  Proof.
    intros f Hf. unfold WfNormalInst. intros rf pcc mem Hrf.
    split; [apply regInst_FuncNormal|].
    specialize (Hf rf pcc Hrf). unfold regInst; cbn.
    revert Hf.
    destruct (f (Build_UserThreadState rf pcc)) as [[rf' pcc']|e]; intros Hf; [|exact I].
    cbn in Hf. destruct Hf as [Hexec [Hreach [Hexec' Hrf']]].
    split; [exact Hexec|].
    split; [apply ValidMemUpdate_refl|].
    split; [apply Hreach|].
    split; [exact Hexec' | exact Hrf'].
  Qed.

  Lemma regInst_FuncSystem : forall f, FuncSystem (liftInst (regInst f)).
  Proof.
    intros f. unfold FuncSystem. intros rf pcc mepcc mtcc exnInfo ts stat ints m1 m2 _.
    unfold liftInst, regInst; cbn.
    destruct (f (Build_UserThreadState rf pcc)) as [uts'|e].
    - split; [reflexivity|]. split; [reflexivity | apply UpdatedMemSame_refl].
    - reflexivity.
  Qed.

  Lemma regInst_WfSystemInst : forall f pcc,
      RegInstOk f -> In Perm.System pcc.(capPerms) -> WfSystemInst (liftInst (regInst f)) pcc.
  Proof.
    intros f pcc Hf Hsys. unfold WfSystemInst. intros rf mem mepcc mtcc exnInfo ts stat ints Hrf.
    split; [apply regInst_FuncSystem|].
    specialize (Hf rf pcc Hrf). unfold liftInst, regInst; cbn.
    revert Hf.
    destruct (f (Build_UserThreadState rf pcc)) as [[rf' pcc']|e]; intros Hf; [|exact I].
    cbn in Hf. destruct Hf as [Hexec [Hreach [Hexec' Hrf']]].
    split; [exact Hexec|].
    split; [exact Hsys|].
    split; [apply ValidMemUpdate_refl|].
    split; [apply (ReachableCaps_app mem (pcc :: capsOfRf rf) (pcc' :: capsOfRf rf')
                                    (mepcc :: mtcc :: capsOfTS ts)); apply Hreach|].
    split; [exact Hexec' | exact Hrf'].
  Qed.

  (** The general result: every register-only instruction whose function is [RegInstOk]
      is a well-formed general instruction. *)
  Lemma regInst_WfGeneralInst : forall f, RegInstOk f -> WfGeneralInst (liftInst (regInst f)).
  Proof.
    intros f Hf. unfold WfGeneralInst. split.
    - exists (regInst f). split; [apply regInst_WfNormalInst; exact Hf|].
      intros rf pcc mem sysCtx _. unfold liftInst, regInst; cbn.
      destruct (f (Build_UserThreadState rf pcc)) as [uts'|e];
        [split; reflexivity | reflexivity].
    - intros pcc Hsys. apply regInst_WfSystemInst; assumption.
  Qed.

  (** *** The no-op

      Requires an executable PCC and advances it; traps, with an empty payload, otherwise. *)
  Definition nopF (uts: UserThreadState) : Result ExnInfo UserThreadState :=
    if execPCCb uts.(thread_pcc)
    then Ok (Build_UserThreadState uts.(thread_rf) (advancePCC uts.(thread_pcc)))
    else Exn [].

  Lemma nopF_ok : RegInstOk nopF.
  Proof.
    intros rf pcc Hrf. unfold nopF; cbn.
    destruct (execPCCb pcc) eqn:Hok; [|exact I].
    apply execPCCb_true in Hok as [Hunsealed Hexec]. cbn.
    split; [exact Hexec|]. split.
    - intros mem c [Hc|Hc].
      + subst c. eapply StepRestrict;
          [apply Refl; left; reflexivity | apply advancePCC_Restrict; exact Hunsealed].
      + apply Refl; right; exact Hc.
    - split; [|exact Hrf].
      cbv [advancePCC updateCapCursor setCapCursor]; cbn; exact Hexec.
  Qed.

  Definition nopInst : UserContext -> SystemContext -> Result ExnInfo (UserContext * SystemContext) :=
    liftInst (regInst nopF).

  Lemma nopInst_wf : WfGeneralInst nopInst.
  Proof. apply regInst_WfGeneralInst, nopF_ok. Qed.

  (** A general instruction: the instruction type is inhabited. *)
  Definition Inst_nop : @Inst _ _ capEncodeDecode := @Inst_General _ _ _ nopInst nopInst_wf.

  (** *** The register move

      [cmove rd rs] copies register [rs] to register [rd] and advances the PCC; it traps
      when either index is out of range or the PCC is not executable.  Capabilities move
      between registers, so this instruction exercises the reachability clause beyond the
      PCC. *)
  Definition cmoveF (rd rs: nat) (uts: UserThreadState) : Result ExnInfo UserThreadState :=
    match nth_error uts.(thread_rf) rs with
    | Some v =>
        if (rd <? length uts.(thread_rf)) && execPCCb uts.(thread_pcc)
        then Ok (Build_UserThreadState (setReg uts.(thread_rf) rd v) (advancePCC uts.(thread_pcc)))
        else Exn []
    | None => Exn []
    end.

  Lemma cmoveF_ok : forall rd rs, RegInstOk (cmoveF rd rs).
  Proof.
    intros rd rs rf pcc Hrf. cbv [cmoveF thread_rf thread_pcc].
    destruct (nth_error rf rs) as [v|] eqn:Hv; [|exact I].
    destruct ((rd <? length rf) && execPCCb pcc) eqn:Hok; [|exact I].
    apply andb_true_iff in Hok as [Hrd Hok].
    apply PeanoNat.Nat.ltb_lt in Hrd.
    apply execPCCb_true in Hok as [Hunsealed Hexec]. cbn.
    split; [exact Hexec|]. split.
    - intros mem c [Hc|Hc].
      + subst c. eapply StepRestrict;
          [apply Refl; left; reflexivity | apply advancePCC_Restrict; exact Hunsealed].
      + apply Refl; right.
        unfold capsOfRf in *. apply listSumToInl_iff in Hc. apply listSumToInl_iff.
        apply setReg_In in Hc as [Hc|Hc].
        * subst v. eapply nth_error_In; exact Hv.
        * exact Hc.
    - split.
      + cbv [advancePCC updateCapCursor setCapCursor]; cbn; exact Hexec.
      + unfold ValidRf in *. rewrite setReg_length; [exact Hrf | exact Hrd].
  Qed.

  Definition cmoveInst (rd rs: nat)
    : UserContext -> SystemContext -> Result ExnInfo (UserContext * SystemContext) :=
    liftInst (regInst (cmoveF rd rs)).

  Lemma cmoveInst_wf : forall rd rs, WfGeneralInst (cmoveInst rd rs).
  Proof. intros; apply regInst_WfGeneralInst, cmoveF_ok. Qed.

  Definition Inst_cmove (rd rs: nat) : @Inst _ _ capEncodeDecode :=
    @Inst_General _ _ _ (cmoveInst rd rs) (cmoveInst_wf rd rs).
End RegisterInstructions.

(** ** Three facts about [Pairwise] and [Subset] *)
Section Pairwise.
  Import Separation.

  Lemma Pairwise1 : forall T (P: T -> T -> Prop) a, Pairwise P [a].
  Proof.
    intros T P a i j xi xj Hij Hi Hj.
    destruct i as [|[|i]], j as [|[|j]]; cbn in Hi, Hj; try discriminate.
    exfalso; apply Hij; reflexivity.
  Qed.

  Lemma Pairwise3 : forall T (P: T -> T -> Prop) a b c,
      P a b -> P b a -> P a c -> P c a -> P b c -> P c b -> Pairwise P [a; b; c].
  Proof.
    intros T P a b c Hab Hba Hac Hca Hbc Hcb i j xi xj Hij Hi Hj.
    destruct i as [|[|[|[|i]]]], j as [|[|[|[|j]]]]; cbn in Hi, Hj; try discriminate;
      try (exfalso; apply Hij; reflexivity);
      injection Hi as Hi; injection Hj as Hj; subst; assumption.
  Qed.

  Lemma Subset_nil : forall A (l: list A), Subset l [] -> l = [].
  Proof.
    intros A [|a l] H; [reflexivity | exfalso; apply (H a); left; reflexivity].
  Qed.
End Pairwise.

(** ** Reachability in a memory without tags

    In a memory whose every tag is clear, [readCap] never yields a capability, so no
    [LoadCap] step is possible; and from capabilities that hold no sealing or unsealing
    key, no [Seal] or [Unseal] step is possible either.  What remains of [ReachableCap] is
    the [Restrict] closure of the original set, which keeps every capability unsealed and
    keyless, inside the addresses of one of the originals, and which does not depend on
    the memory at all.  These two lemmas are what the configuration's well-formedness
    rests on. *)
Section Untagged.
  Context [ISA: ISA_params].
  Context {machineTypeParams: MachineTypeParams}.
  Context {capEncodeDecode: CapEncodeDecode}.

  Definition NoKeysUnsealed (c: Cap) : Prop :=
    c.(capSealed) = None /\ c.(capSealingKeys) = [] /\ c.(capUnsealingKeys) = [].

  Lemma ReachableCap_untagged_inv :
    forall (mem: FullMemory) origSet c,
      (forall capa, snd mem capa = false) ->
      (forall x, In x origSet -> NoKeysUnsealed x) ->
      ReachableCap mem origSet c ->
      NoKeysUnsealed c /\ exists x, In x origSet /\ Subset c.(capAddrs) x.(capAddrs).
  Proof.
    intros mem origSet c Htags Horig H. unfold NoKeysUnsealed in *. induction H.
    - split; [apply Horig; exact inPf|]. exists c; split; [exact inPf | apply Subset_refl].
    - destruct IHReachableCap as [[Hs [Hsk Huk]] [x [Hx Hsub]]].
      unfold Restrict in yz. rewrite Hs in yz. cbn in yz.
      destruct yz as [Heq Hperms Hcs Hcbs Hsk' Huk' Haddrs Hkp Hkcs Hkcbs].
      split; [|exists x; split; [exact Hx | intros a Ha; apply Hsub; apply Haddrs; exact Ha]].
      split; [unfold SealEq in Heq; rewrite Heq; exact Hs|].
      split; apply Subset_nil; [rewrite <- Hsk; exact Hsk' | rewrite <- Huk; exact Huk'].
    - exfalso. destruct xyz as [_ _ [capa [_ Hread]] _].
      cbv [readCap readMemTagCap bytesToCap] in Hread. rewrite Htags in Hread.
      cbn in Hread. discriminate.
    - exfalso. destruct IHReachableCap1 as [[_ [Hsk _]] _].
      destruct xyz as [k [Hk _]]. rewrite Hsk in Hk. destruct Hk.
    - exfalso. destruct IHReachableCap1 as [[_ [_ Huk]] _].
      destruct xyz as [k [Hk _]]. rewrite Huk in Hk. destruct Hk.
  Qed.

  Lemma ReachableCap_untagged_anymem :
    forall (mem: FullMemory) origSet c,
      (forall capa, snd mem capa = false) ->
      (forall x, In x origSet -> NoKeysUnsealed x) ->
      ReachableCap mem origSet c ->
      forall mem', ReachableCap mem' origSet c.
  Proof.
    intros mem origSet c Htags Horig H.
    enough (NoKeysUnsealed c /\ forall mem', ReachableCap mem' origSet c) as [_ Hr] by exact Hr.
    unfold NoKeysUnsealed in *. induction H.
    - split; [apply Horig; exact inPf|]. intros mem'; apply Refl; exact inPf.
    - destruct IHReachableCap as [[Hs [Hsk Huk]] IH].
      split.
      + unfold Restrict in yz. rewrite Hs in yz. cbn in yz.
        destruct yz as [Heq Hperms Hcs Hcbs Hsk' Huk' Haddrs Hkp Hkcs Hkcbs].
        split; [unfold SealEq in Heq; rewrite Heq; exact Hs|].
        split; apply Subset_nil; [rewrite <- Hsk; exact Hsk' | rewrite <- Huk; exact Huk'].
      + intros mem'. eapply StepRestrict; [apply IH | exact yz].
    - exfalso. destruct xyz as [_ _ [capa [_ Hread]] _].
      cbv [readCap readMemTagCap bytesToCap] in Hread. rewrite Htags in Hread.
      cbn in Hread. discriminate.
    - exfalso. destruct IHReachableCap1 as [[_ [Hsk _]] _].
      destruct xyz as [k [Hk _]]. rewrite Hsk in Hk. destruct Hk.
    - exfalso. destruct IHReachableCap1 as [[_ [_ Huk]] _].
      destruct xyz as [k [Hk _]]. rewrite Huk in Hk. destruct Hk.
  Qed.

  Lemma ReachableAddr_In :
    forall (mem: FullMemory) caps a sz p cs cbs,
      ReachableAddr mem caps a sz p cs cbs -> 0 < sz ->
      exists c, ReachableCap mem caps c /\ In a c.(capAddrs).
  Proof.
    intros * H Hsz. destruct H as [c cPf a sz ina notSealed].
    exists c; split; [exact cPf|]. apply ina. apply in_seq; lia.
  Qed.
End Untagged.

(** ** The configuration and the initial machine

    Sixteen registers and eight-byte capabilities (CHERIoT's RV32E base and 64-bit
    capabilities); bytes and keys are natural numbers.  The capability encoding stays a
    parameter: no tagged memory is ever read, so no encoding is ever exercised, and the
    results hold for every encoding. *)
Instance witnessISA : ISA_params := {| ISA_LG_CAPSIZE_BYTES := 3; ISA_NREGS := 16 |}.
Instance witnessMTP : MachineTypeParams := {| Byte := nat; Key := nat |}.

Import Configuration.
Import Separation.

Section WitnessConfiguration.
  Context {capEncodeDecode: CapEncodeDecode}.

  (** *** The data

      Three disjoint regions: code at 0 to 63, the export table at 64 to 71, the stack at
      128 to 191.  One compartment, which is the switcher, holding only its code
      capability.  One thread, starting at the code's base, with registers holding bytes,
      a stack capability over the stack region, one trusted-stack frame naming the single
      export entry, and the configuration's trap capability.  No tag is set anywhere. *)
  Definition codePCC : Cap := mkUnsealedPCC (seq 0 64) 0.

  Definition exportTableCap : Cap :=
    {| capSealed := Some (inr 0);
       capPerms := [Perm.Load];
       capCanStore := [];
       capCanBeStored := [Local; NonLocal];
       capSealingKeys := [];
       capUnsealingKeys := [];
       capAddrs := seq 64 8;
       capKeepPerms := [];
       capKeepCanStore := [];
       capKeepCanBeStored := [];
       capCursor := 64 |}.

  Definition exportEntry0 : ExportEntry :=
    {| exportEntryOffset := 0;
       exportEntryStackSize := 0;
       exportEntryNumArgs := 0;
       exportEntryInterruptStatus := InterruptsEnabled |}.

  Definition compartment0 : Compartment :=
    {| compartmentPCC := codePCC;
       compartmentCGP := None;
       compartmentImports := [];
       compartmentErrorHandlers := [];
       compartmentExports := [exportEntry0];
       compartmentExportTableAddrs := seq 64 8;
       compartmentSealingCaps := [] |}.

  Definition switcher0 : SwitcherConfig :=
    {| Switcher_compartmentIdx := 0;
       Switcher_AddrOf_compartment_switcher_entry := 0;
       Switcher_AddrOf_exception_entry_asm := 4;
       Switcher_AddrOf_switcher_after_compartment_call := 8;
       Switcher_AddrOf_error_handler_return := 12;
       Switcher_key := 0 |}.

  Definition csp0 : Cap := mkCSP 128 64 128.

  Definition threadMeta0 : InitialThreadMetadata :=
    {| initThreadCSP := csp0; initThreadCompartment := 0 |}.

  Definition initMemory : FullMemory := (fun _ => 0, fun _ => false).

  Definition config0 : Config :=
    {| configCompartments := [compartment0];
       configThreads := [threadMeta0];
       configInitMemory := initMemory;
       configSwitcher := switcher0 |}.

  Definition rf0 : RegisterFile := repeat (inr [] : CapOrBytes) 16.

  Definition frame0 : TrustedStackFrame :=
    {| trustedStackFrame_CSP := csp0;
       trustedStackFrame_calleeExportTable := exportTableCap;
       trustedStackFrame_errorCounter := 0 |}.

  Definition thread0 : Thread :=
    {| thread_userState := {| thread_rf := rf0; thread_pcc := codePCC |};
       thread_systemState :=
         {| thread_mepcc := codePCC;
            thread_mtcc := MTCC config0;
            thread_exceptionInfo := [];
            thread_trustedStack := {| trustedStack_frames := [frame0] |};
            thread_alive := ThreadAlive |} |}.

  Definition machine0 : Machine :=
    {| machine_memory := initMemory;
       machine_interruptStatus := InterruptsEnabled;
       machine_threads := [thread0];
       machine_curThreadId := 0 |}.

  (** The export-table lookup: a capability inside compartment 0's export table denotes
      its first export entry.  Well formed in the sense the properties file states. *)
  Definition lookup0 (config: Config) (cap: Cap) : option (nat * nat) :=
    match nth_error config.(configCompartments) 0 with
    | Some c =>
        match nth_error c.(compartmentExports) 0 with
        | Some _ =>
            if forallb (fun a => existsb (Nat.eqb a) c.(compartmentExportTableAddrs)) cap.(capAddrs)
            then Some (0, 0) else None
        | None => None
        end
    | None => None
    end.

  Lemma lookup0_wf : WFLookupExportTableCompartmentId lookup0.
  Proof.
    unfold WFLookupExportTableCompartmentId, lookup0. intros config cap cid eid H.
    destruct (nth_error (configCompartments config) 0) as [c|] eqn:Hc; [|discriminate].
    destruct (nth_error (compartmentExports c) 0) as [e|] eqn:He; [|discriminate].
    destruct (forallb _ _) eqn:Hall; [|discriminate].
    injection H as H1 H2; subst cid eid.
    exists c, e. split; [exact Hc|]. split; [|exact He].
    intros a Ha. rewrite forallb_forall in Hall. specialize (Hall a Ha).
    apply existsb_exists in Hall as [b [Hb Hab]]. apply PeanoNat.Nat.eqb_eq in Hab. subst. exact Hb.
  Qed.

  (** *** Well-formedness of the configuration *)
  Lemma initMemory_untagged : forall capa, snd initMemory capa = false.
  Proof. reflexivity. Qed.

  Lemma codePCC_NoKeys : NoKeysUnsealed codePCC.
  Proof. split; [reflexivity | split; reflexivity]. Qed.

  Lemma capsOfCompartment0 : capsOfCompartment compartment0 = [codePCC].
  Proof. reflexivity. Qed.

  Lemma caps0_NoKeys : forall x, In x (capsOfCompartment compartment0) -> NoKeysUnsealed x.
  Proof. rewrite capsOfCompartment0. intros x [Hx|[]]; subst; exact codePCC_NoKeys. Qed.

  Lemma wf_compartment0 : WFCompartment config0 compartment0.
  Proof.
    constructor.
    - intros a [p [cs [cbs [Hra _]]]].
      apply ReachableAddr_In in Hra as [c [Hc Hin]]; [|lia].
      apply (ReachableCap_untagged_inv _ _ _ initMemory_untagged caps0_NoKeys) in Hc
        as [_ [x [Hx Hsub]]].
      rewrite capsOfCompartment0 in Hx. destruct Hx as [Hx|[]]; subst x.
      cbv [compartmentFootprint compartment0 compartmentPCC compartmentCGP from_option].
      rewrite app_nil_r. exact (Hsub a Hin).
    - intros cap Hcap mem'.
      exact (ReachableCap_untagged_anymem _ _ _ initMemory_untagged caps0_NoKeys Hcap _).
    - split; [reflexivity|]. split; [apply Subset_refl | intros [H|[]]; discriminate].
    - intros cgp H; cbv [compartment0 compartmentCGP] in H; discriminate.
    - intros cap Hcap Hsentry.
      apply (ReachableCap_untagged_inv _ _ _ initMemory_untagged caps0_NoKeys) in Hcap
        as [[Hs _] _].
      unfold isSentry in Hsentry. rewrite Hs in Hsentry. discriminate.
    - intros cap Hcap Hsealed.
      apply (ReachableCap_untagged_inv _ _ _ initMemory_untagged caps0_NoKeys) in Hcap
        as [[Hs _] _].
      unfold isSealedDataCap in Hsealed. rewrite Hs in Hsealed. discriminate.
    - intros e [].
    - constructor.
    - constructor.
  Qed.

  Lemma wf_config0 : WFConfig config0.
  Proof.
    constructor.
    - cbv [Separated ConfigFootprints compartmentFootprint stackFootprint exportTableFootprint
           config0 configCompartments configThreads compartment0 compartmentPCC compartmentCGP
           compartmentExportTableAddrs threadMeta0 initThreadCSP from_option map
           codePCC mkUnsealedPCC csp0 mkCSP mkCSP' capAddrs].
      apply Pairwise3; intros t H1 H2; repeat rewrite app_nil_r in *;
        apply in_seq in H1, H2; lia.
    - constructor; [exact wf_compartment0 | constructor].
    - exists compartment0; split; [reflexivity | exact I].
    - intros c id cap [Hc [Hin _]]. apply nth_error_In in Hc.
      destruct Hc as [Hc|[]]. subst c. destruct Hin.
  Qed.

  (** *** Validity of the initial machine *)
  Lemma validCSP0 : ValidCSP csp0.
  Proof. exists 128, 64, 128. split; [apply in_seq; lia | reflexivity]. Qed.

  Lemma capsOfUserTS_thread0 : capsOfUserTS thread0.(thread_userState) = [codePCC].
  Proof. reflexivity. Qed.

  Lemma valid_thread0 : @ValidInitialThread _ _ _ lookup0 config0 threadMeta0 thread0.
  Proof.
    constructor.
    - exists compartment0. split; [reflexivity|].
      intros c Hc. rewrite capsOfUserTS_thread0 in Hc.
      eapply ReachableCapIncrease; [exact Hc|].
      intros x [Hx|[]]; subst x. right. rewrite capsOfCompartment0. left; reflexivity.
    - exists frame0. split; [reflexivity|]. constructor.
      + exists 0. reflexivity.
      + split; [apply validCSP0 | apply RestrictRefl].
    - intros capa _. reflexivity.
    - apply validCSP0.
  Qed.

  Lemma valid_machine0 : @ThreadIsolatedMonotonicity.ValidInitialMachine _ _ _ lookup0 config0 machine0.
  Proof.
    split.
    - constructor.
      + reflexivity.
      + constructor; [exact valid_thread0 | constructor].
      + constructor; [cbn; lia | constructor; [constructor; reflexivity | constructor]].
      + intros t [Ht|[]] _; subst t; constructor; reflexivity.
    - apply Pairwise1.
  Qed.

  (** *** The theorem, instantiated

      With a fetch of four bytes at the cursor and a decoder that returns the no-op for
      every byte string, the theorem's three hypotheses are met, and its conclusion is a
      closed statement about this machine. *)
  Definition fetch0 (mem: FullMemory) (a: Addr) : list Addr := seq a 4.
  Definition decode0 (bytes: list Byte) : @Inst _ _ capEncodeDecode := @Inst_nop _ _ capEncodeDecode.
  Definition exn0 : EXNInfo := [].

  Definition theoremInstance :=
    @ThreadIsolatedMonotonicity.ThreadIsolatedMonotonicity
      _ _ _ fetch0 decode0 exn0 lookup0 config0 machine0 wf_config0 valid_machine0.

  (** *** One step

      The machine is not stuck at its initial state: the fetch at the PCC's cursor is in
      bounds, the decoder returns the no-op, and the no-op succeeds, so the machine takes
      one [MachineStep] to the state with the PCC advanced, and the event is a
      same-domain one ([Ev_SameThread 0 Ev_General]).  The theorem's conclusion is
      therefore exercised on a non-empty same-domain trace, not only on the empty one. *)
  Definition thread1 : Thread :=
    {| thread_userState := {| thread_rf := rf0; thread_pcc := advancePCC codePCC |};
       thread_systemState := thread0.(thread_systemState) |}.

  Definition machine1 : Machine :=
    {| machine_memory := initMemory;
       machine_interruptStatus := InterruptsEnabled;
       machine_threads := [thread1];
       machine_curThreadId := 0 |}.

  Lemma machine0_step :
    MachineStep fetch0 decode0 exn0 (machine0, []) (machine1, [Ev_SameThread 0 Ev_General]).
  Proof.
    apply Spec.Step_SameThread.
    apply (Spec.SameThreadStepOk fetch0 decode0 exn0 machine0 machine1 Ev_General).
    - reflexivity.
    - intros n Hn. destruct n; [exfalso; apply Hn; reflexivity | reflexivity].
    - exists thread0, thread1.(thread_userState), thread1.(thread_systemState).
      split; [reflexivity|]. split; [reflexivity|]. split; [|reflexivity].
      apply Spec.GoodThreadStep.
      change (Subset (seq 0 4) (seq 0 64) /\ In 0 (seq 0 64)
              /\ isSealed codePCC = false /\ In Perm.Exec codePCC.(capPerms)).
      split; [intros a Ha; apply in_seq in Ha; apply in_seq; lia|].
      split; [apply in_seq; lia|].
      split; [reflexivity | left; reflexivity].
  Qed.
End WitnessConfiguration.
