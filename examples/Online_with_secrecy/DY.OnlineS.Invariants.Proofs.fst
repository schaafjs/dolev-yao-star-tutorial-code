module DY.OnlineS.Invariants.Proofs

open Comparse
open DY.Core
open DY.Lib

open DY.Simplified
open DY.Extend

open DY.OnlineS.Protocol
open DY.OnlineS.Invariants

#set-options "--fuel 0 --ifuel 1 --z3rlimit 25  --z3cliopt 'smt.qi.eager_threshold=100'"

/// In this module, we show that
/// the three protocol steps (send_ping, receive_ping_and_send_ack, and receive_ack)
/// maintain the protocol invariants.
///
/// For every step s we show a lemma of the form:
/// trace_invariant tr ==> trace_invariant ( trace after step s )



/// The invariant lemma for the first step `send_ping`

val send_ping_invariant:
  alice:principal -> bob:principal -> keys_sid:state_id ->
  tr:trace ->
  Lemma
  ( requires trace_invariant tr
  )
  (ensures (
    let (_ , tr_out) = send_ping alice bob keys_sid tr in
    trace_invariant tr_out
  ))
(* The proof works by showing that the trace invariant is maintained
   by every traceful action in the step.
   So we replicate the actions of the step and show trace_invariant after each.
   
   (Note that we are now in the "Lemma context",
   so we have to unfold the monadic lets and composition.)
*)
let send_ping_invariant alice bob keys_sid  tr =
  (* The first action is generating the nonce n_a.
  
     Note that we can't use let* here since we are not in the traceful monad.
     Thus, we have to pass the trace `tr` explicitly as last argument.
     And we get back the new trace `tr_rand`.
  *)
  let (n_a, tr_rand) = gen_rand_labeled (nonce_label alice bob) tr in
  (* That the trace invariant holds after this action,
     can be shown automatically.

    There is a corresponding lemma in `DY.Core.Trace.Manipulation`:
    `mk_rand_trace_invariant`.
    It comes with an SMT Pattern an hence is applied automatically.
  *)
  assert(trace_invariant tr_rand);

  // Defining the abstract message does not change the trace,
  // so we don't have to show anything.
  let ping = Ping {p_alice = alice; p_n_a = n_a} in 

  (* The call of `pk_enc_for` in the traceful + option monad 
     has to be unfolded:
     * We pass the current trace `tr_rand` as las argument
     * We need to make a case distinction on the resulting option
       and show trace_invariant in each case separately
  *)
  match pk_enc_for alice bob keys_sid key_tag ping tr_rand with
  | (None, _) -> ( 
      (* If encryption fails, the trace is not changed,
         and hence the resulting trace after send_ping is tr_rand.
         Since we already showed trace_invariant for tr_rand,
         we don't have to show anything else in this case.

        If you want to check this,
        you can uncomment the next lines
      *)
      // let (_ , tr_out) = send_ping alice bob keys_sid tr in 
      // assert(tr_out == tr_rand);
      // assert(trace_invariant tr_out);
      ()
    )
  | (Some ping_encrypted, tr_enc) -> (
      (* If encryption succeeds, we get a new trace `tr_enc`.
         With the lemma `pk_enc_for_invariant` in `DY.Simplified`,
         we have that trace_invariant holds for tr_enc.

         Observe, that this lemma can be shown automatically.
         Hence, we don't even have to call it here.
      *)
      assert(trace_invariant tr_enc);

      (* The next traceful action is sending the encrypted message.

         Again, we have to pass the current trace `tr_enc` as last argument.

      *)
      let (msg_ts, tr_msg) = send_msg ping_encrypted tr_enc in
      (* To show trace_invariant after sending the message (for `tr_msg`),
         we look at the lemma `send_msg_invariant` in `DY.Core.Trace.Manipulation`
         which looks very promising.
         However, that lemma has an additional pre-condition requiring that
         the message needs to be publishable.
         (That corresponds to the intuition that everything on the trace 
         is readable by the attacker.)

         So to call this lemma, we have to show `is_publishable tr_enc ping_encrypted`.
         Looking at `DY.Simplified`, we find the lemma `pk_enc_for_is_publishable`,
         which gives a bunch of pre-conditions for the plaintext (serialized `ping`) 
         under which the ciphertext `ping_encrypted` is publishable.
         We show each of those pre-conditions.
      *)
          (* The first is `has_pki_invariant`.

             It is a technical requirement on the protocol invariants 
             which we are not explaining here.

             In `DY.OnlineS.Invariants` we have the lemma `protocol_invariants_p_has_pki_invariant`
             showing this requirement.
          *)
          assert(has_pki_invariant);

          (* The next requirement for `pk_enc_for_is_publishable` is `bytes_invariant tr_enc (serialize ping)`.

             TODO              
          *)
          serialize_wf_lemma message (is_knowable_by (nonce_label alice bob) tr_rand) ping;

          (* The next two pre-conditions say
             that the serialized ping should be readable by Alice and Bob.
             (Ignore the `long_term_key_label` for now.)

             TODO: they are resolved with the same serialize_wf_lemma
          *)

          (* Finally, we need to show the disjunction of
             * the pkenc_pred holds for the serialized ping or
             * the serialized ping is publishable

             In our case, the first is true, i.e., the encryption prediate is satisfied.
             The predicate requires that the nonce contained in the ping
             has the label `nonce_label alice' bob'`, where
             * alice' is the name in the first component of the ping and
             * bob' is the participant whos key is used for encryption.

             Since we generate the nonce n_a in the beginning of this step
             with the label `nonce_label alice bob`,
             put the same alice in the first component of the ping
             and use the key of bob for encryption (in pk_enc_for),
             we satisfy the predicate.
          *)
          assert(pkenc_pred.pred tr_rand (long_term_key_type_to_usage (LongTermPkEncKey key_tag) bob) (serialize message ping));
      (* Now we showed all pre-conditions of `pk_enc_for_is_publishable`
         and can call this lemma to show that ping_encrypted is publishable.

         Together with the `send_msg_invariant` lemma, 
         we then obtain that `tr_msg` satisfies tha trace invariant.
      *)
      pk_enc_for_is_publishable tr_rand alice bob keys_sid key_tag ping;
      assert(trace_invariant tr_msg);

      (* The last traceful action in this step is starting a new session *)
      let st = SentPing {sp_bob = bob; sp_n_a = n_a} in
      let (sid, tr_sess) = start_new_session alice st tr_msg in
      (* `start_new_session` is just calling `new_session_id` and then `set_state`.
         So we have to check that both of those maintain the trace invariant.

         For `new_session_id` we find the lemma 
         `new_session_id_same_trace` in `DY.Core.Trace.Manipulation`
         which says that the trace is not changed.
         Hence it trivially maintains the trace invariant.
         It comes with an SMT pattern, so it is applied automatically.

         In the same file, we have the lemma `set_state_invariant`,
         which gives an additional pre-condition 
         for when the trace after the state was set satisfies the trace invariant.
         This pre-condition is that the new state must satisfy the state predicate.

         The state predicate for the SentPing state requires that
         the nonce stored in the state has the label `nonce_label alice' bob'`, where
         * alice' is the storing principal
         * bob' is the name stored in the first component of the state

         Similarly to above,
         we generated the nonce wit the label `nonce_label alice bob` and
         alice is storing the new state, and
         bob is stored in the first component of the state.
         So the state prediate is satisfied
      *)
      assert(state_predicate_p.pred tr_msg alice sid st);
       (* With this, we have all pre-conditions of `set_state_invariant`.
          Since that lemma comes with an SMT pattern,
          it is applied automatically.
       *)
      assert(trace_invariant tr_sess)
  )

(* The above proof was very detailed.
   In fact, most of the proof is done automatically by F*
   and we can remove all of the asserts.

   If we just keep the necessary calls to lemmas,
   we end up with the following very short proof.
*)
val send_ping_invariant_short_version:
  alice:principal -> bob:principal -> keys_sid:state_id ->
  tr:trace ->
  Lemma
  ( requires trace_invariant tr
  )
  (ensures (
    let (_ , tr_out) = send_ping alice bob keys_sid tr in
    trace_invariant tr_out
  ))
let send_ping_invariant_short_version alice bob keys_sid  tr =
  let (n_a, tr_rand) = gen_rand_labeled (nonce_label alice bob) tr in
  let ping = Ping {p_alice = alice; p_n_a = n_a} in 
  serialize_wf_lemma message (is_knowable_by (nonce_label alice bob) tr_rand) ping;
  pk_enc_for_is_publishable tr_rand alice bob keys_sid key_tag ping

val decode_ping_proof:
  tr:trace ->
  bob:principal -> keys_sid:state_id ->
  msg:bytes ->
  Lemma
  (requires (
    trace_invariant tr
    /\ bytes_invariant tr msg
  ))
  (ensures (
    match decode_ping bob keys_sid msg tr with
    | (None, _) -> True
    | (Some png, _) -> (
        let n_a = png.p_n_a in
        bytes_invariant tr n_a /\
        is_knowable_by (nonce_label png.p_alice bob) tr n_a /\
        ( is_publishable tr n_a
        \/ (pkenc_pred.pred tr (long_term_key_type_to_usage (LongTermPkEncKey key_tag) bob) (serialize message (Ping png)))
        )
    )
  ))
let decode_ping_proof tr bob keys_sid msg =
    match decode_ping bob keys_sid msg tr with
    | (None, _) -> ()
    | (Some png, _) -> (
        bytes_invariant_pk_dec_with_key_lookup tr #message #parseable_serializeable_bytes_message bob keys_sid key_tag msg;
        let plain = serialize message (Ping png) in
        parse_wf_lemma message (bytes_invariant tr) plain;
        FStar.Classical.move_requires (parse_wf_lemma message (is_publishable tr)) plain
    )
  

val receive_ping_and_send_ack_invariant:
  bob:principal -> keys_sid:global_sess_ids -> ts:timestamp ->
  tr:trace ->
  Lemma
  ( requires trace_invariant tr
  )
  (ensures (
    let (_ , tr_out) = receive_ping_and_send_ack bob keys_sid ts tr in
    trace_invariant tr_out
  ))
let receive_ping_and_send_ack_invariant bob bob_keys_sid msg_ts tr =
  match recv_msg msg_ts tr with
  | (None, _ ) -> ()
  | (Some msg, _) -> (
      match decode_ping bob bob_keys_sid.private_keys msg tr with
      | (None, _) -> ()
      | (Some png, _) -> (
           let n_a = png.p_n_a in
           let alice = png.p_alice in
          decode_ping_proof tr bob bob_keys_sid.private_keys msg;
          assert(is_knowable_by (nonce_label alice bob) tr n_a);
           let ack = Ack {a_n_a = n_a} in
           match pk_enc_for bob alice bob_keys_sid.pki key_tag ack tr with
           | (None, _) -> ()
           | (Some ack_encrypted, tr_ack) ->(
                assert(trace_invariant tr_ack);
                
                serialize_wf_lemma message (bytes_invariant tr) (Ping png);
                assert(bytes_invariant tr (serialize message (Ping png)));
                serialize_wf_lemma message (bytes_invariant tr) (ack);
                assert(bytes_invariant tr (serialize message ack));

                serialize_wf_lemma message (is_knowable_by (nonce_label alice bob) tr) (ack);
                pk_enc_for_is_publishable tr bob alice bob_keys_sid.pki key_tag ack;
                let (ack_ts, tr_msg) = send_msg ack_encrypted tr_ack in
                assert(trace_invariant tr_msg);
                let st = (SentAck {sa_alice = png.p_alice; sa_n_a = png.p_n_a}) in
                let (sess_id, tr_sess) = start_new_session bob st tr_msg in
                assert(trace_invariant tr_sess)
           )
      )
  )

val receive_ack_invariant:
  alice:principal -> keys_sid:state_id -> msg_ts:timestamp ->
  tr:trace ->
  Lemma
  (requires
    trace_invariant tr
  )
  (ensures (
    let (_, tr_out) = receive_ack alice keys_sid msg_ts tr in
    trace_invariant tr_out
  ))
let receive_ack_invariant alice keys_sid msg_ts tr =
  match recv_msg msg_ts tr with
  | (None, _ ) -> ()
  | (Some msg, _) -> (
      match decode_ack alice keys_sid msg tr with
      | (None, _) -> ()
      | (Some ack, tr_ack) -> (
          let n_a = ack.a_n_a in
          assert(trace_invariant tr_ack);
          match lookup_state #state alice
    (fun st -> SentPing? st && (SentPing?.ping st).sp_n_a = n_a) tr with
          | (None, _) -> ()
          | (Some (SentPing st, sid), _) -> ()
  ))
