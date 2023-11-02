module DPE.Messages.Parse
open Pulse.Lib.Pervasives
open DPE
open CBOR.Spec
open CBOR.Pulse
open CDDL.Pulse
module Spec = DPE.Messages.Spec
module SZ = FStar.SizeT
module U8 = FStar.UInt8
module A = Pulse.Lib.Array
assume
val drop (p:vprop)
    : stt unit p (fun _ -> emp)

#push-options "--ext 'pulse:env_on_err'"

assume
val dbg : vprop

open Pulse.Lib.Stick

let emp_inames_disjoint (t:inames)
  : Lemma 
    (ensures (t /! emp_inames))
    [SMTPat (Set.disjoint t emp_inames)]
  = admit()

```pulse
ghost
fn elim_implies (_:unit) (#p #q:vprop)
   requires `@(p @==> q) ** p
   ensures q
{
  open Pulse.Lib.Stick;
  rewrite `@(p @==> q) as (stick #emp_inames p q);
  elim_stick #emp_inames #emp_inames p q;
}
```

```pulse
fn finish (c:read_cbor_success_t)
          (#p:perm)
          (#v:erased (raw_data_item))
          (#s:erased (Seq.seq U8.t))
          (#rem:erased (Seq.seq U8.t))
  requires `@((raw_data_item_match c.read_cbor_payload v **
               A.pts_to c.read_cbor_remainder #p rem) @==>
              A.pts_to input #p s) **
            raw_data_item_match c.read_cbor_payload v **
            A.pts_to c.read_cbor_remainder #p rem **
            uds_is_enabled
  returns _:option ctxt_hndl_t
  ensures A.pts_to input #p s
{
   elim_implies ()  #(raw_data_item_match c.read_cbor_payload v **
                            A.pts_to c.read_cbor_remainder #p rem)
                            #(A.pts_to input #p s);
    drop uds_is_enabled;
    None #ctxt_hndl_t
}
```

assume Fits_u64 : squash (SZ.fits_u64)

let impl_session_message : impl_typ Spec.session_message =
  impl_t_array (
    impl_array_group3_concat
      (impl_array_group3_item impl_uint)
      (impl_array_group3_item impl_bytes)
  )

assume val impl_command_message' : impl_typ Spec.command_message'

module U64 = FStar.UInt64

noeq
type dpe_cmd = {
  dpe_cmd_sid: U64.t;
  dpe_cmd_cid: U64.t;
  dpe_cmd_args: cbor;
}

#push-options "--z3rlimit 64 --query_stats" // to let z3 cope with CDDL specs
#restart-solver

noextract
let parse_dpe_cmd_args_postcond
  (cid: U64.t)
  (vargs: raw_data_item)
  (vcmd: raw_data_item)
  (rem: Seq.seq U8.t)
: Tot prop
= data_item_wf deterministically_encoded_cbor_map_key_order vcmd /\
  Spec.command_message vcmd /\ (
    let Array [Int64 _ cid'; vargs'] = vcmd in
    cid == cid' /\
    vargs == vargs'
  ) /\
  Seq.length rem == 0
  
noextract
let parse_dpe_cmd_postcond
  (sid: U64.t)
  (cid: U64.t)
  (vargs: raw_data_item)
  (vsess: raw_data_item)
  (_: Seq.seq U8.t)
: Tot prop
= data_item_wf deterministically_encoded_cbor_map_key_order vsess /\
  Spec.session_message vsess /\ (
    let Array [Int64 _ sid'; String _ cmd] = vsess in
    sid == sid' /\ (
    exists vcmd rem .
    cmd == serialize_cbor vcmd `Seq.append` rem /\
    parse_dpe_cmd_args_postcond cid vargs vcmd rem
  ))

noextract
let parse_dpe_cmd_failure_postcond
 (s: Seq.seq U8.t)
: prop
=
  ~ (exists vsess rem .
    s == serialize_cbor vsess `Seq.append` rem /\ (
      exists sid cid vargs .
      parse_dpe_cmd_postcond sid cid vargs vsess rem
    )
  )


let parse_dpe_cmd_post
  (len:SZ.t)
  (input:A.larray U8.t (SZ.v len))
  (s:erased (Seq.seq U8.t))
  (p:perm)
  (res: option dpe_cmd)
: vprop
= match res with
  | None -> A.pts_to input #p s ** pure (parse_dpe_cmd_failure_postcond s)
  | Some cmd -> exists_ (fun vargs ->
      raw_data_item_match cmd.dpe_cmd_args vargs **
      (raw_data_item_match cmd.dpe_cmd_args vargs @==>
        A.pts_to input #p s
      ) **
      pure (
        exists (vsess: raw_data_item) (rem: Seq.seq U8.t) .
        Ghost.reveal s == serialize_cbor vsess `Seq.append` rem /\
        parse_dpe_cmd_postcond cmd.dpe_cmd_sid cmd.dpe_cmd_cid vargs vsess rem
      )
    )

let parse_dpe_cmd_fail_case_2
  (s: Seq.seq U8.t)
  (vsess: raw_data_item)
  (rem: Seq.seq U8.t)
: Lemma
  (requires (
    s == serialize_cbor vsess `Seq.append` rem /\
    data_item_wf deterministically_encoded_cbor_map_key_order vsess /\
    Spec.session_message vsess /\ (
    let Array [_; String _ msg] = vsess in
    (forall vmsg rem2 . (msg == serialize_cbor vmsg `Seq.append` rem2 /\ data_item_wf deterministically_encoded_cbor_map_key_order vmsg) ==>
      Spec.command_message' vmsg == false
    )
  )))
  (ensures (
    parse_dpe_cmd_failure_postcond s
  ))
= serialize_cbor_with_test_correct vsess rem (fun vc' vrem1' ->
    exists sid cid vargs .
    parse_dpe_cmd_postcond sid cid vargs vc' vrem1'
  )

let parse_dpe_cmd_fail_case_3
  (s: Seq.seq U8.t)
  (vsess: raw_data_item)
  (rem: Seq.seq U8.t)
  (vmsg: raw_data_item)
  (rem2: Seq.seq U8.t)
: Lemma
  (requires (
    s == serialize_cbor vsess `Seq.append` rem /\
    data_item_wf deterministically_encoded_cbor_map_key_order vsess /\
    Spec.session_message vsess /\ (
    let Array [_; String _ msg] = vsess in
    msg == serialize_cbor vmsg `Seq.append` rem2 /\
    data_item_wf deterministically_encoded_cbor_map_key_order vmsg /\
    Spec.command_message' vmsg == true /\
    Seq.length rem2 <> 0
  )))
  (ensures (
    parse_dpe_cmd_failure_postcond s
  ))
= serialize_cbor_with_test_correct vmsg rem2 (fun vmsg' vrem2' ->
    exists cid vargs .
    parse_dpe_cmd_args_postcond cid vargs vmsg' vrem2'
  );
  serialize_cbor_with_test_correct vsess rem (fun vc' vrem1' ->
    exists sid cid vargs .
    parse_dpe_cmd_postcond sid cid vargs vc' vrem1'
  )


#push-options "--z3rlimit 64 --query_stats" // to let z3 cope with CDDL specs
#restart-solver

```pulse
fn parse_dpe_cmd (len:SZ.t)
                      (input:A.larray U8.t (SZ.v len))
                      (#s:erased (Seq.seq U8.t))
                      (#p:perm)
    requires
        A.pts_to input #p s
    returns res:option dpe_cmd
    ensures
      parse_dpe_cmd_post len input s p res
{
    let rc = read_deterministically_encoded_cbor_with_typ impl_session_message input len;
    match rc
    {
      ParseError ->
      {
        unfold (read_deterministically_encoded_cbor_with_typ_post Spec.session_message input p s ParseError); 
        fold (parse_dpe_cmd_post len input s p None);
        None #dpe_cmd
      }
      ParseSuccess c ->
      {
        unfold (read_deterministically_encoded_cbor_with_typ_post Spec.session_message input p s (ParseSuccess c));
        with vc . assert (raw_data_item_match c.read_cbor_payload vc);
        with vrem1 . assert (A.pts_to c.read_cbor_remainder #p vrem1);
        stick_consume_r ()
          #(raw_data_item_match c.read_cbor_payload vc)
          #(A.pts_to c.read_cbor_remainder #p vrem1)
          #(A.pts_to input #p s)
        ;
        let i0 = cbor_array_index c.read_cbor_payload 0sz;
        let cbor_int = destr_cbor_int64 i0;
        let sid = cbor_int.cbor_int_value;
        elim_implies ();
        let i1 = cbor_array_index c.read_cbor_payload 1sz;
        stick_trans ();
        let cbor_str = destr_cbor_string i1;
        stick_trans ();
        with cs . assert (A.pts_to cbor_str.cbor_string_payload #cbor_str.permission cs);
        let msg_rc = read_deterministically_encoded_cbor_with_typ impl_command_message' cbor_str.cbor_string_payload (SZ.of_u64 cbor_str.cbor_string_length);
        match msg_rc
        {
          ParseError ->
          {
            unfold (read_deterministically_encoded_cbor_with_typ_post Spec.command_message' cbor_str.cbor_string_payload cbor_str.permission cs ParseError);
            elim_implies ();
            parse_dpe_cmd_fail_case_2 s vc vrem1;
            fold (parse_dpe_cmd_post len input s p None);
            None #dpe_cmd
          }
          ParseSuccess msg ->
          {
            unfold (read_deterministically_encoded_cbor_with_typ_post Spec.command_message' cbor_str.cbor_string_payload cbor_str.permission cs (ParseSuccess msg));
            with vmsg . assert (raw_data_item_match msg.read_cbor_payload vmsg);
            with vrem2 . assert (A.pts_to msg.read_cbor_remainder #cbor_str.permission vrem2);
            stick_consume_r ()
              #(raw_data_item_match msg.read_cbor_payload vmsg)
              #(A.pts_to msg.read_cbor_remainder #cbor_str.permission vrem2)
              #(A.pts_to cbor_str.cbor_string_payload #cbor_str.permission cs)
            ;
            stick_trans ();
            if (msg.read_cbor_remainder_length <> 0sz) {
              elim_implies ();
              parse_dpe_cmd_fail_case_3 s vc vrem1 vmsg vrem2;
              fold (parse_dpe_cmd_post len input s p None);
              None #dpe_cmd
            } else {
              let cmd_id_cbor = cbor_array_index msg.read_cbor_payload 0sz;
              let cmd_id_int = destr_cbor_int64 cmd_id_cbor;
              let cmd_id = cmd_id_int.cbor_int_value;
              elim_implies ();
              let cmd_args = cbor_array_index msg.read_cbor_payload 1sz;
              stick_trans ();
              with vargs . assert (raw_data_item_match cmd_args vargs);

              let res = Mkdpe_cmd sid cmd_id cmd_args;
(*  // FIXME: WHY WHY WHY does the following record literal FAIL with "List.combine: list lengths differ"
              let res = {
                dpe_cmd_id = cmd_id;
                dpe_cmd_args = cmd_args;
              };
*)              
              rewrite (raw_data_item_match cmd_args vargs ** `@(raw_data_item_match cmd_args vargs @==> A.pts_to input #p s)) // FIXME: should `fold` honor projectors and not just `match`?
                as (raw_data_item_match res.dpe_cmd_args vargs ** `@(raw_data_item_match res.dpe_cmd_args vargs @==> A.pts_to input #p s));
              fold (parse_dpe_cmd_post len input s p (Some res));
              Some res
            }
          }
        }
      }
    }
}
```

#pop-options
