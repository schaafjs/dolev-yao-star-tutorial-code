module DY.NSL.Data

open Comparse
open DY.Core
open DY.Lib

let nonce_label alice bob = join (principal_label alice) (principal_label bob)

(* Messages *)

[@@ with_bytes bytes]
type msg1_t = {
  alice: principal;
  n_a : bytes;
}

[@@ with_bytes bytes]
type msg2_t = {
  bob : principal;
  n_a : bytes;
  n_b : bytes;
}

[@@ with_bytes bytes]
type msg3_t = {
  n_b : bytes;
}

[@@ with_bytes bytes]
type message_t =
  | Msg1: (msg1:msg1_t) -> message_t
  | Msg2: (msg2:msg2_t) -> message_t
  | Msg3: (msg3:msg3_t) -> message_t

%splice [ps_msg1_t] (gen_parser (`msg1_t))
%splice [ps_msg2_t] (gen_parser (`msg2_t))
%splice [ps_msg3_t] (gen_parser (`msg3_t))

%splice [ps_message_t] (gen_parser (`message_t))

instance parseable_serializeable_bytes_message_t: parseable_serializeable bytes message_t =
  mk_parseable_serializeable ps_message_t

(* States *)

[@@ with_bytes bytes]
type sent_msg1_t = {
  bob : principal;
  n_a : bytes;
}

[@@ with_bytes bytes]
type sent_msg2_t = {
  alice : principal;
  n_a : bytes;
  n_b : bytes;
}

[@@ with_bytes bytes]
type sent_msg3_t = {
  bob : principal;
  n_a : bytes;
  n_b : bytes;
}

[@@ with_bytes bytes]
type rcvd_msg3_t = {
  alice : principal;
  n_a : bytes;
  n_b : bytes;
}

[@@ with_bytes bytes]
type state_t =
  | SentMsg1: (sentmsg1:sent_msg1_t) -> state_t
  | SentMsg2: (sentmsg2:sent_msg2_t) -> state_t
  | SentMsg3: (sentmsg3:sent_msg3_t) -> state_t
  | RcvdMsg3: (receivedmsg3:rcvd_msg3_t) -> state_t

%splice [ps_sent_msg1_t] (gen_parser(`sent_msg1_t))
%splice [ps_sent_msg2_t] (gen_parser(`sent_msg2_t))
%splice [ps_sent_msg3_t] (gen_parser(`sent_msg3_t))
%splice [ps_rcvd_msg3_t] (gen_parser(`rcvd_msg3_t))
%splice [ps_state_t] (gen_parser(`state_t))

instance parseable_serializeable_bytes_state_t: parseable_serializeable bytes state_t = 
  mk_parseable_serializeable ps_state_t

instance local_state_state_t: local_state state_t = {
  tag = "Online.State";
  format = parseable_serializeable_bytes_state_t;
}

// Global tag constant
let key_tag = "Online.Key"

[@@ with_bytes bytes]
type ev_init_t = {
  alice:principal;
  bob:principal;
  n_a:bytes
}

[@@ with_bytes bytes]
type ev_respond1_t = {
  alice:principal;
  bob:principal;
  n_a:bytes;
  n_b:bytes
}

type event_t =
  | Initiating:  ev_init_t -> event_t
  | Responding1: ev_respond1_t -> event_t

%splice [ps_ev_init_t] (gen_parser (`ev_init_t))
%splice [ps_ev_respond1_t] (gen_parser (`ev_respond1_t))
%splice [ps_event_t] (gen_parser (`event_t))

instance event_event_t: event event_t = {
  tag = "NSL.Event";
  format = mk_parseable_serializeable ps_event_t;
}
