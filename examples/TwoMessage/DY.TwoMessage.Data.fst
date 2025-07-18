module DY.TwoMessage.Data

open Comparse
open DY.Core
open DY.Lib

(* Messages *)

[@@ with_bytes bytes]
type ping_t = {
  alice: principal;
  n_a : bytes;
}

[@@ with_bytes bytes]
type ack_t = {
  n_a : bytes;
}

[@@ with_bytes bytes]
type message_t =
  | Ping: (ping:ping_t) -> message_t
  | Ack:  (ack:ack_t) -> message_t

%splice [ps_ping_t] (gen_parser (`ping_t))
%splice [ps_ack_t] (gen_parser (`ack_t))
%splice [ps_message_t] (gen_parser (`message_t))

instance parseable_serializeable_bytes_message_t: parseable_serializeable bytes message_t =
  mk_parseable_serializeable ps_message_t

(* States *)

[@@ with_bytes bytes]
type sent_ping_t = {
  bob : principal;
  n_a : bytes;
}

[@@ with_bytes bytes]
type sent_ack_t = {
  alice: principal;
  n_a : bytes;
}

[@@ with_bytes bytes]
type received_ack_t = {
  bob : principal;
  n_a : bytes;
}

[@@ with_bytes bytes]
type state_t =
  | SentPing: (ping:sent_ping_t) -> state_t
  | SentAck: (ack:sent_ack_t) -> state_t
  | ReceivedAck: (rack:received_ack_t) -> state_t

%splice [ps_sent_ping_t] (gen_parser (`sent_ping_t))
%splice [ps_sent_ack_t] (gen_parser (`sent_ack_t))
%splice [ps_received_ack_t] (gen_parser (`received_ack_t))
%splice [ps_state_t] (gen_parser (`state_t))

instance parseable_serializeable_bytes_state_t: parseable_serializeable bytes state_t =
  mk_parseable_serializeable ps_state_t

instance local_state_state_t: local_state state_t = {
  tag = "TwoMessage.State";
  format = parseable_serializeable_bytes_state_t;
}
