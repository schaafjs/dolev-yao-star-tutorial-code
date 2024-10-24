module DY.OnlineS.Tmp

open Comparse
open DY.Core
open DY.Lib

#set-options "--fuel 0 --ifuel 1 --z3rlimit 25  --z3cliopt 'smt.qi.eager_threshold=100'"

[@@ with_bytes bytes]
type cont_t = {
  p: principal;
  n: bytes
}

[@@ with_bytes bytes]
type state = 
 | S: cont_t -> state
 | S2: principal -> bytes -> state

%splice [ps_cont_t] (gen_parser (`cont_t))
%splice [ps_cont_t_is_well_formed] (gen_is_well_formed_lemma (`cont_t))


%splice [ps_state] (gen_parser (`state))
%splice [ps_state_is_well_formed] (gen_is_well_formed_lemma (`state))

instance parseable_serializeable_bytes_state: parseable_serializeable bytes state = mk_parseable_serializeable ps_state

instance local_state_state: local_state state = {
  tag = "S";
  format = parseable_serializeable_bytes_state;
}

instance crypto_usages_p : crypto_usages = default_crypto_usages

let crypto_p : crypto_predicates = { 
  default_crypto_predicates with 
  pkenc_pred = { 
    pred = (fun tr sk_usage msg -> True); 
    pred_later = (fun tr1 tr2 pk msg -> ()) 
  } 
}

instance crypto_invariants_p: crypto_invariants = {
  usages = crypto_usages_p;
  preds =  crypto_p
}

let state_predicate_nsl: local_state_predicate state = {
  pred = (fun tr prin sess_id st ->
    match st with
    | S cont -> 
        is_knowable_by (principal_label prin) tr cont.n
    | S2 _ n ->    
        is_knowable_by (principal_label prin) tr n
  );
  pred_later = (fun tr1 tr2 prin sess_id st -> ());
  pred_knowable = (fun tr prin sess_id st ->
    match st with
    | S cont -> 
    serialize_wf_lemma state (is_knowable_by (principal_label prin) tr) st
    | S2 _ n ->         serialize_wf_lemma state (is_knowable_by (principal_label prin) tr) st
    );
}
